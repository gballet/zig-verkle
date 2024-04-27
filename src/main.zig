const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const verkle_crypto = @import("verkle-crypto");
const banderwagon = verkle_crypto.banderwagon;
const Element = banderwagon.Element;
const Fr = banderwagon.Fr;
const CRS = verkle_crypto.crs.CRS;
const copyForwards = std.mem.copyForwards;
const types = @import("./types.zig");

const Slot = types.Slot;
const Stem = types.Stem;
const Key = types.Key;
const Hash = types.Hash;

const ExtStatus = enum {
    Empty,
    Other,
    Present,
};

const ProofItems = struct {
    cis: ArrayList(*Element),
    yis: ArrayList(?Fr),
    zis: ArrayList(u8),
    // don't support stateful proofs just yet
    // fis: *ArrayList(ArrayList(*Fr)),

    esses: ArrayList(u8),
    poas: ArrayList(Stem),
    values: ArrayList(?*Slot),

    const Self = @This();

    fn merge(self: *ProofItems, other: *const ProofItems) !void {
        _ = other;
        _ = self;
    }
};

const LastLevelNode = struct {
    // TODO remove pointer
    values: [256]?*Slot,
    stem: Stem,
    crs: *CRS,
    c1: ?*Element,
    c2: ?*Element,
    depth: u8,
    commitment: ?*Element,

    fn computeSuffixNodeCommitment(crs: *CRS, values: []const ?*Slot) !Element {
        if (values.len != 128) {
            return error.InvalidValueArrayLength;
        }

        var vals: [256]Fr = undefined;
        for (values, 0..) |value, i| {
            if (value != null) {
                var data: [Fr.BytesSize]u8 = [_]u8{0} ** Fr.BytesSize;

                // lsb
                copyForwards(u8, data[0..16], value.?[0..16]);
                data[16] = 1; // leaf marker
                vals[2 * i] = Fr.fromBytes(data);

                // msb
                copyForwards(u8, data[0..16], value.?[16..]);
                data[16] = 0; // clear leaf marker
                vals[2 * i + 1] = Fr.fromBytes(data);
            } else {
                vals[2 * i] = Fr.zero();
                vals[2 * i + 1] = Fr.zero();
            }
        }

        return crs.commit(vals[0..]);
    }

    fn isZero(stem: []const u8) bool {
        for (stem) |v| {
            if (v != 0)
                return false;
        }

        return true;
    }

    fn computeCommitment(self: *const LastLevelNode) !Element {
        var vals: [4]Fr = undefined;

        vals[0] = Fr.fromInteger(1);

        var stem = [_]u8{0} ** Fr.BytesSize;
        copyForwards(u8, stem[0..], self.stem[0..31]);
        vals[1] = Fr.fromBytes(stem);

        const c1 = try computeSuffixNodeCommitment(self.crs, self.values[0..128]);
        const c2 = try computeSuffixNodeCommitment(self.crs, self.values[128..]);

        vals[2] = c1.mapToScalarField();
        vals[3] = c2.mapToScalarField();

        return self.crs.commit(vals[0..]);
    }

    fn get_proof_items(self: *const LastLevelNode, keys: []Key) !ProofItems {
        var has_c1 = false;
        var has_c2 = false;
        const proof_items = ProofItems{};
        for (keys) |key| {
            if (key[31] < 128 and !has_c1) {
                has_c1 = true;
                // add c1 to proof item

            }
            if (key[31] >= 128 and !has_c2) {
                has_c2 = true;
                // add c2 to proof item
            }
            _ = self.values[key[31]];
        }

        return proof_items;
    }
};

const BranchNode = struct {
    children: [256]Node,
    depth: u8,
    count: u8,
    crs: *CRS,
    commitment: ?*Element,

    fn computeCommitment(self: *const BranchNode) anyerror!Element {
        if (self.commitment != null) {
            // TODO return a pointer instead
            return self.commitment.?.*;
        }

        var vals: [256]Fr = undefined;

        for (self.children, 0..) |child, i| {
            if (child != .empty) {
                const point = try child.commitment();
                vals[i] = point.mapToScalarField();
            } else {
                vals[i] = Fr.zero();
            }
        }
        return self.crs.commit(vals[0..]);
    }

    fn get_proof_items(self: *const BranchNode, keys: []Key) !ProofItems {
        const groupstart = 0;
        // TODO initialize with my proof info
        var proof_items = ProofItems{};
        while (groupstart < keys.len) {
            var groupend = groupstart;
            while (groupend < keys.len and keys[groupend][self.depth] == keys[groupstart][self.depth]) {
                groupend += 1;
            }

            const child_proof_items = self.children[keys[groupstart][self.depth]].get_proof_items(keys[groupstart..groupend]);

            proof_items.merge(child_proof_items);
        }
    }
};

fn newll(key: Key, value: *const Slot, allocator: Allocator, crs: *CRS) !*LastLevelNode {
    const slot = key[31];
    var ll = try allocator.create(LastLevelNode);
    ll.values = [_]?*Slot{null} ** 256;
    ll.stem = [_]u8{0} ** 31;
    copyForwards(u8, ll.stem[0..], key[0..31]);
    ll.values[slot] = try allocator.create(Slot);
    copyForwards(u8, ll.values[slot].?[0..], value[0..]);
    ll.crs = crs;
    return ll;
}

fn newemptyll(stem: Stem, depth: u8, allocator: Allocator, crs: *CRS) !*LastLevelNode {
    var ll = try allocator.create(LastLevelNode);
    ll.values = [_]?*Slot{null} ** 256;
    ll.stem = [_]u8{0} ** 31;
    ll.depth = depth;
    std.mem.copyForwards(u8, ll.stem[0..], stem[0..31]);
    ll.crs = crs;
    return ll;
}

const PoAStub = struct {
    stem: *const Stem,
    commitment: ?*Element,

    fn computeCommitment(self: *const PoAStub) anyerror!Element {
        return self.commitment.?.*;
    }
};

const Node = union(enum) {
    last_level: *LastLevelNode,
    branch: *BranchNode,
    hash: Hash,

    empty: struct {},
    unresolved: struct {}, // indicate a subtree that was not resolved
    poa_stub: PoAStub, // indicate an unresolved LEAF tree whose stem is known

    fn new(allocator: Allocator, crs: *CRS) !@This() {
        var br = try allocator.create(BranchNode);
        for (br.children, 0..) |_, idx| {
            br.children[idx] = Node{ .empty = .{} };
        }
        br.crs = crs;
        br.depth = 0;
        br.count = 0;
        br.commitment = null;
        return @This(){ .branch = br };
    }

    fn insert(self: *Node, key: Key, value: *const Slot, allocator: Allocator, crs: *CRS) !void {
        return self.insert_with_depth(key, value, allocator, 0, crs);
    }

    fn get(self: *Node, key: Key) !?*Slot {
        return switch (self.*) {
            .empty => null,
            .hash => error.ReadFromHash,
            .last_level => |ll| {
                if (!std.mem.eql(u8, key[0..31], ll.stem[0..31])) {
                    return null;
                }

                return ll.values[key[31]];
            },
            .branch => |br| return br.children[key[br.depth]].get(key),
            .unresolved, .poa_stub => error.ReadFromUnresolved,
        };
    }

    fn insert_with_depth(self: *Node, key: Key, value: *const Slot, allocator: Allocator, depth: u8, crs: *CRS) anyerror!void {
        return switch (self.*) {
            .empty => {
                self.* = @unionInit(Node, "last_level", try newll(key, value, allocator, crs));
            },
            .hash => error.InsertIntoHash,
            .unresolved => error.InsertIntoUnresolved,
            .last_level => |ll| {
                // Check if the stems are the same, if so, then just place the value
                // in the corresponding slot, as the final extension tree has been
                // reached.
                const diffidx = std.mem.indexOfDiff(u8, ll.stem[0..], key[0..31]);
                if (diffidx == null) {
                    ll.values[key[31]] = try allocator.create(Slot);
                    copyForwards(u8, ll.values[key[31]].?[0..], value[0..]);
                    return;
                }

                var br = try allocator.create(BranchNode);
                br.children = [_]Node{Node{ .empty = .{} }} ** 256;
                br.depth = depth;
                br.count = 2;
                br.children[ll.stem[br.depth]] = Node{ .last_level = ll };
                br.crs = crs;
                self.* = @unionInit(Node, "branch", br);
                // Recurse into the child, if this is empty then it will be turned
                // into a last_level node in the recursing .empty case, and if the
                // next byte in the key are the same, it will recurse into another
                // .last_level case, potentially doing so over the whole stem.
                return br.children[key[br.depth]].insert_with_depth(key, value, allocator, depth + 1, crs);
            },
            .branch => |br| br.children[key[br.depth]].insert(key, value, allocator, br.crs),
            // TODO : implement
            .poa_stub => return error.ErrTODO,
        };
    }

    fn tear_down(self: *Node, allocator: Allocator) void {
        switch (self.*) {
            .empty => {},
            .last_level => |ll| {
                for (ll.values) |v| {
                    if (v != null) {
                        allocator.free(v.?);
                    }
                }

                allocator.destroy(ll);
            },
            .branch => |br| {
                for (br.children, 0..) |_, i| {
                    br.children[i].tear_down(allocator);
                }

                allocator.destroy(br);
            },
            .hash, .unresolved, .poa_stub => {},
        }
    }

    fn commitment(self: *const Node) !Element {
        return switch (self.*) {
            .empty => Element.identity(),
            .hash => |_| error.NeedToReworkHashedNodes,
            .last_level => |ll| ll.computeCommitment(),
            .branch => |br| br.computeCommitment(),
            .unresolved => error.CannotComputeUnresolvedCommitment,
            .poa_stub => |ps| ps.computeCommitment(),
        };
    }

    // assume that keys are sorted
    fn get_proof_items(self: *const Node, keys: [][32]u8) !ProofItems {
        return switch (self.*) {
            .branch => |br| br.get_proof_items(keys),
            .last_level => |ll| ll.get_proof_items(keys),
            _ => error.NotImplemented,
        };
    }

    fn toDot(self: *const Node, str: *std.ArrayList(u8), path: []const u8, parent: []const u8) !void {
        const comm = try self.commitment();
        const hash = comm.mapToScalarField().toBytes();
        var mebuf = [_]u8{0} ** 100;
        const me = try std.fmt.bufPrint(mebuf[0..], "{s}{s}", .{ @tagName(self.*), path });

        switch (self.*) {
            .branch => |br| {
                if (br.depth == 0) {
                    _ = try str.writer().write("digraph D {\n");
                }

                try std.fmt.format(str.writer(), "{s} [label=\"I: {s}\"]\n", .{ me, std.fmt.fmtSliceHexLower(&hash) });

                for (br.children, 0..) |child, childidx| {
                    if (child != .empty) {
                        var buf = [_]u8{0} ** 64;
                        const child_path = try std.fmt.bufPrint(buf[0..], "{s}{x:0>2}", .{ path, childidx });

                        try child.toDot(str, child_path, me);
                    }
                }

                if (br.depth == 0) {
                    _ = try str.writer().write("}");
                }
            },
            .last_level => |ll| {
                try std.fmt.format(str.writer(), "{s} [label=\"I: {s}\\nS: {}\"]\n", .{ me, std.fmt.fmtSliceHexLower(&hash), std.fmt.fmtSliceHexLower(&ll.stem) });

                for (ll.values, 0..) |val, validx| {
                    if (val) |value| {
                        try std.fmt.format(str.writer(), "value{s}{x:0>2} [label=\"{s}\"]\n{s} -> value{s}{x:0>2}\n", .{ path, validx, std.fmt.fmtSliceHexLower(value), me, path, validx });
                    }
                }
            },
            .hash => {
                try std.fmt.format(str.writer(), "{s} [label=\"H: {s}\"]\n", .{ me, hash });
            },
            .unresolved => {
                try std.fmt.format(str.writer(), "{s} [label=\"?\"]\n", .{me});
            },
            else => {}, // ignore other node types for now
        }

        if (parent.len > 0) {
            try std.fmt.format(str.writer(), "{s} -> {s}\n", .{ parent, me });
        }
    }
};

const SuffixDiff = struct {
    suffix: u8,
    current_value: ?Slot,
    new_value: ?Slot,
};

const SuffixDiffs = []SuffixDiff;

const StemStateDiff = struct {
    stem: Stem,
    suffix_diffs: SuffixDiffs,
};
const StateDiffs = []StemStateDiff;

const IPAProof = struct {
    c_l: [8]Element,
    c_r: [8]Element,
    final_evaluation: Element,
};

const VerkleProof = struct {
    other_stems: ArrayList(Stem),
    depth_and_presence: []u8,
    commitments_by_path: ArrayList(Element),
    d: Element,
    ipa_proof: IPAProof,
};

const ExecutionWitness = struct {
    state_diff: ArrayList(StemStateDiff),
    verkle_proof: VerkleProof,

    allocator: std.mem.Allocator,

    fn deinit(self: *ExecutionWitness) void {
        for (self.state_diff.items) |state_diff| {
            self.allocator.free(state_diff.suffix_diffs);
        }
        self.state_diff.deinit();

        self.verkle_proof.other_stems.deinit();
        self.verkle_proof.commitments_by_path.deinit();
        self.allocator.free(self.verkle_proof.depth_and_presence);

        self.allocator.destroy(self);
    }
};

fn newEmptyBranchNode(depth: u8, crs: *CRS, allocator: Allocator) !*BranchNode {
    var br: *BranchNode = try allocator.create(BranchNode);
    br.children = [_]Node{Node{ .empty = .{} }} ** 256;
    br.crs = crs;
    br.depth = depth;
    br.commitment = null;
    br.count = 0;
    return br;
}

pub fn preTreeFromWitness(parent_root_comm: *Element, statediffs: StateDiffs, depths_and_ext_statuses: []const u8, poa_stems: []const Stem, commitments: []Element, alloc: Allocator, crs: *CRS) !Node {
    var root = try Node.new(alloc, crs);
    errdefer root.tear_down(alloc);
    root.branch.commitment = parent_root_comm;
    var statediff_index: usize = 0;
    var poa_stem_index: usize = 0;
    var commitment_index: usize = 0;

    for (depths_and_ext_statuses) |depth_and_ext_status| {
        const depth = depth_and_ext_status >> 3;
        const ext_status: ExtStatus = @enumFromInt(depth_and_ext_status & 3);

        switch (ext_status) {
            .Empty => {
                const stem = statediffs[statediff_index].stem;

                // sanity check: ensure all `current_values` are empty
                for (statediffs[statediff_index].suffix_diffs) |suffix_diff| {
                    if (suffix_diff.current_value != null) {
                        return error.InvalidProofEmptyStemHasNonEmptySuffix;
                    }
                }

                // Walk the tree depth in order to consume non-initialized commitments
                var node: *BranchNode = root.branch;
                for (0..depth - 1) |d| {
                    // Add next node in the path if it doesn't exist, unless this is the last one as this is a proof of absence
                    if (node.children[stem[d]] == .empty) {
                        node.children[stem[d]] = .{ .branch = try newEmptyBranchNode(@as(u8, @intCast(d)) + 1, crs, alloc) };
                    }

                    node = node.children[stem[d]].branch;

                    if (node.commitment == null) {
                        // consume commitment
                        node.commitment = &commitments[commitment_index];
                        commitment_index += 1;
                    }
                }
            },
            .Other => {
                const stem = &poa_stems[poa_stem_index];

                // Walk the tree depth in order to consume non-initialized commitments
                var node: *BranchNode = root.branch;
                for (0..depth - 1) |d| {
                    // Add next node in the path if it doesn't exist, unless this is the last one as this is a proof of absence
                    if (node.children[stem[d]] == .empty) {
                        node.children[stem[d]] = .{ .branch = try newEmptyBranchNode(@as(u8, @intCast(d)) + 1, crs, alloc) };
                    }

                    node = node.children[stem[d]].branch;

                    if (node.commitment == null) {
                        node.commitment = &commitments[commitment_index];
                        commitment_index += 1;
                    }
                }

                // end of the line: insert a proof of stem marker
                node.children[stem[depth]] = .{ .poa_stub = .{ .stem = stem, .commitment = &commitments[commitment_index] } };
                commitment_index += 1;

                // "consume" a PoA stem
                poa_stem_index += 1;
            },
            .Present => {
                const stem = statediffs[statediff_index].stem;

                // Walk the tree depth in order to consume non-initialized commitments
                var node: *BranchNode = root.branch;
                for (0..depth) |d| {
                    // Add next node in the path if it doesn't exist, unless this is the last one as this is a proof of absence
                    if (node.children[stem[d]] == .empty) {
                        node.children[stem[d]] = .{ .branch = try newEmptyBranchNode(@as(u8, @intCast(d)) + 1, crs, alloc) };
                    }

                    node = node.children[stem[d]].branch;

                    if (node.commitment == null) {
                        node.commitment = &commitments[commitment_index];
                        commitment_index += 1;
                    }
                }

                // end of the line: insert a leaf with all present values
                var ll = try newemptyll(stem, depth, alloc, crs);
                ll.commitment = &commitments[commitment_index];
                commitment_index += 1;
                node.children[stem[depth]] = Node{ .last_level = ll };
                for (statediffs[statediff_index].suffix_diffs) |suffix_diff| {
                    // will be left to `null` if suffix_dixx.current_value is `null`.
                    if (suffix_diff.current_value) |sdiff| {
                        ll.values[suffix_diff.suffix] = try alloc.create(Slot);
                        std.mem.copyForwards(u8, ll.values[suffix_diff.suffix].?, &sdiff);
                    }

                    // consume another commitment if c1 or c2 is needed, and hasn't been set.
                    if (suffix_diff.suffix < 128) {
                        if (ll.c1 == null) {
                            ll.c1 = &commitments[commitment_index];
                            commitment_index += 1;
                        }
                    } else {
                        if (ll.c2 == null) {
                            ll.c2 = &commitments[commitment_index];
                            commitment_index += 1;
                        }
                    }
                }
            },
        }

        // "consume" a state diff
        statediff_index += 1;
    }

    // Sanity check: ensure all commitments have been consumed.
    if (commitment_index != commitments.len) {
        std.debug.print("invalid commitment number: {} != {}\n", .{ commitment_index, commitments.len });
        return error.InvalidProofTooManyCommitments;
    }

    return root;
}

fn executionWitnessFromJSON(payload: []const u8, allocator: std.mem.Allocator) !*ExecutionWitness {
    const json = std.json;

    // Temporary structure used to hold the deserialized json,
    // which has hex string representation of every number in
    // the struct.
    const T = struct {
        stateDiff: []struct {
            stem: []u8,
            suffixDiffs: []struct {
                suffix: u8,
                currentValue: ?[]u8,
                newValue: ?[]u8,
            },
        },
        verkleProof: struct {
            otherStems: [][]const u8,
            depthExtensionPresent: []const u8,
            commitmentsByPath: [][]const u8,
            d: []const u8,
            ipaProof: struct {
                cl: [][]const u8,
                cr: [][]const u8,
                finalEvaluation: []const u8,
            },
        },
    };

    var decoded = try json.parseFromSlice(T, allocator, payload, .{ .ignore_unknown_fields = true });
    defer decoded.deinit();

    var ew = try allocator.create(ExecutionWitness);
    ew.allocator = allocator;
    ew.state_diff = try ArrayList(StemStateDiff).initCapacity(allocator, decoded.value.stateDiff.len);

    for (decoded.value.stateDiff) |statediff| {
        var new_stem_state_diff: StemStateDiff = StemStateDiff{ .stem = [_]u8{0} ** 31, .suffix_diffs = try allocator.alloc(SuffixDiff, statediff.suffixDiffs.len) };
        _ = try std.fmt.hexToBytes(new_stem_state_diff.stem[0..], statediff.stem[2..]);
        for (statediff.suffixDiffs, 0..) |suffixdiff, i| {
            new_stem_state_diff.suffix_diffs[i].suffix = suffixdiff.suffix;
            if (suffixdiff.currentValue) |cv| {
                new_stem_state_diff.suffix_diffs[i].current_value = [_]u8{0} ** 32;
                _ = try std.fmt.hexToBytes(new_stem_state_diff.suffix_diffs[i].current_value.?[0..], cv[2..]);
            } else {
                // TODO check if I can use a default value instead, but that has some downstream implications that I need to master
                new_stem_state_diff.suffix_diffs[i].current_value = null;
            }
            if (suffixdiff.newValue) |nv| {
                new_stem_state_diff.suffix_diffs[i].new_value = [_]u8{0} ** 32;
                _ = try std.fmt.hexToBytes(new_stem_state_diff.suffix_diffs[i].new_value.?[0..], nv[2..]);
            } else {
                new_stem_state_diff.suffix_diffs[i].new_value = null;
            }
        }
        try ew.state_diff.append(new_stem_state_diff);
    }

    ew.verkle_proof.commitments_by_path = try ArrayList(Element).initCapacity(allocator, decoded.value.verkleProof.commitmentsByPath.len);
    for (decoded.value.verkleProof.commitmentsByPath) |c| {
        var bytes: [32]u8 = undefined;
        _ = try std.fmt.hexToBytes(&bytes, c[2..]);
        const new_c = try Element.fromBytes(bytes);
        try ew.verkle_proof.commitments_by_path.append(new_c);
    }
    ew.verkle_proof.other_stems = try ArrayList(Stem).initCapacity(allocator, decoded.value.verkleProof.otherStems.len);
    for (decoded.value.verkleProof.otherStems) |o| {
        var stem: Stem = undefined;
        _ = try std.fmt.hexToBytes(&stem, o[2..]);
        try ew.verkle_proof.other_stems.append(stem);
    }

    ew.verkle_proof.depth_and_presence = try allocator.alloc(u8, (decoded.value.verkleProof.depthExtensionPresent.len - 2) / 2);
    _ = try std.fmt.hexToBytes(ew.verkle_proof.depth_and_presence, decoded.value.verkleProof.depthExtensionPresent[2..]);

    return ew;
}

test "rebuild tree from proof" {
    const execution_witness_json = @embedFile("./kaustinen_5_block_34171.json");
    var ew = try executionWitnessFromJSON(execution_witness_json, testing.allocator);
    defer ew.deinit();
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();

    var root_hash: Hash = undefined;
    _ = try std.fmt.hexToBytes(root_hash[0..], "67db21d8e7ce2b4783d8a94eab44140d84360504400f47aeb7a205fff683afe5");
    var root_comm = try Element.fromBytes(root_hash);
    var tree = try preTreeFromWitness(&root_comm, ew.state_diff.items, ew.verkle_proof.depth_and_presence, ew.verkle_proof.other_stems.items, ew.verkle_proof.commitments_by_path.items, testing.allocator, &crs);
    defer tree.tear_down(testing.allocator);

    var list = std.ArrayList(u8).init(testing.allocator);
    defer list.deinit();
    try tree.toDot(&list, "", "");
    std.debug.print("{s}\n", .{list.items[0..]});

    var absentkey: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(absentkey[0..], "038c7bc853b037e3fc63b284f422c115891b9a79bfee6c87e7006f3ca4e1a800");
    const absent = try tree.get(absentkey);
    try testing.expect(absent == null);

    var presentkey: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(presentkey[0..], "0e88cc6bf033a3ff779335e720d5a7edf907cc70ab7ff31375cd485db779fc00");
    const present = try tree.get(presentkey);
    try testing.expect(present != null);
}

test "testing toDot" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);
    var list = std.ArrayList(u8).init(testing.allocator);
    defer list.deinit();

    try root.toDot(&list, "", "");
    std.debug.print("{s}\n", .{list.items[0..]});
}

test "inserting into hash raises an error" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = Node{ .hash = [_]u8{0} ** 32 };
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try testing.expectError(error.InsertIntoHash, root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs));
}

test "insert into empty tree" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    switch (root.*) {
        Node.branch => |br| switch (br.children[0]) {
            Node.last_level => |ll| {
                for (ll.values, 0..) |v, i| {
                    if (i == 0) {
                        try testing.expect(v != null);
                    } else {
                        try testing.expect(v == null);
                    }
                }
            },
            else => return error.InvalidNodeType,
        },
        else => return error.InvalidNodeType,
    }
}

test "insert into a last_level node, difference in suffix" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    try root.insert([_]u8{0} ** 31 ++ [1]u8{1}, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    switch (root.*) {
        Node.branch => |br| switch (br.children[0]) {
            Node.last_level => |ll| {
                for (ll.values, 0..) |v, i| {
                    if (i < 2) {
                        try testing.expect(v != null);
                    } else {
                        try testing.expect(v == null);
                    }
                }
            },
            else => return error.InvalidNodeType,
        },
        else => return error.InvalidNodeType,
    }
}

test "insert into a last_level node, difference in stem" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    try root.insert([1]u8{1} ++ [_]u8{0} ** 31, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    switch (root.*) {
        Node.branch => |br| {
            for (br.children, 0..) |child, i| {
                switch (child) {
                    Node.last_level => |ll| {
                        try testing.expect(i < 2);
                        for (ll.values, 0..) |v, j| {
                            if (j == 0) {
                                try testing.expect(v != null);
                            } else {
                                try testing.expect(v == null);
                            }
                        }
                    },
                    Node.empty => try testing.expect(i >= 2),
                    else => return error.InvalidNodeType,
                }
            }
        },
        else => return error.InvalidNodeType,
    }
}

test "insert into a last_level node, difference in last byte of stem" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    try root.insert([_]u8{0} ** 30 ++ [2]u8{ 1, 0 }, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    var br: *BranchNode = root.branch;
    while (true) {
        if (br.depth < 30) {
            for (br.children, 0..) |child, i| {
                if (i == 0) try testing.expect(child == .branch) else try testing.expect(child == .empty);
            }
            br = br.children[0].branch;
        } else if (br.depth == 30) {
            for (br.children, 0..) |child, i| {
                if (i < 2) try testing.expect(child == .last_level) else try testing.expect(child == .empty);
            }
            break;
        } else {
            try testing.expect(false);
        }
    }
}

test "insert into a branch node" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    try root.insert([1]u8{1} ++ [_]u8{0} ** 31, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    const br: *BranchNode = root.branch;
    try testing.expect(br.children[0] == .last_level);
    try testing.expect(br.children[1] == .last_level);
    var i: usize = 2;
    while (i < 256) : (i += 1) {
        try testing.expect(br.children[i] == .empty);
    }
}

test "compute root commitment of a last_level node" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{1} ** 32, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "compute root commitment of a last_level node, with 0 key" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "compute root commitment of a branch node" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
    try root.insert([_]u8{1} ** 32, &value, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "get inserted value from a tree" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    const key1 = [_]u8{0} ** 32;
    var value1 = [_]u8{11} ** 32;
    try root.insert(key1, &value1, testing.allocator, &crs);
    const key2 = [1]u8{1} ++ [_]u8{0} ** 31;
    var value2 = [_]u8{22} ** 32;
    try root.insert(key2, &value2, testing.allocator, &crs);
    defer root.tear_down(testing.allocator);

    var val = try root.get(key1);
    _ = try testing.expect(val != null);
    _ = try testing.expect(std.mem.eql(u8, val.?, &value1));
    val = try root.get(key2);
    _ = try testing.expect(val != null);
    _ = try testing.expect(std.mem.eql(u8, val.?, &value2));
}

test "check verkle-crypto can be imported" {
    const expect = testing.expect;

    var point = Element.generator();

    try expect(Element.equal(point, Element.generator()));

    Element.double(&point, point);

    try expect(!Element.equal(point, Element.generator()));
}

test "compatibility with go-verkle" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    defer root.tear_down(testing.allocator);

    // step 1: try an empty tree
    const r = try root.commitment();
    const r_bytes = r.toBytes();

    const empty_root = [_]u8{0} ** 32;

    try std.testing.expectEqual(empty_root, r_bytes);
    const zero_key = [_]u8{0} ** 32;

    try root.insert(zero_key, &zero_key, testing.allocator, &crs);

    const r_single = try root.commitment();
    const r_single_bytes = r_single.toBytes();

    var single_leaf_root: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(single_leaf_root[0..], "6b630905ce275e39f223e175242df2c1e8395e6f46ec71dce5557012c1334a5c");

    try std.testing.expectEqual(single_leaf_root, r_single_bytes);
}

test "compare simple tree root with that of rust implementation" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    defer root.tear_down(testing.allocator);

    const test_account_keys = [_]Key{
        Key{ 245, 110, 100, 66, 36, 244, 87, 100, 144, 207, 224, 222, 20, 36, 164, 83, 34, 18, 82, 155, 254, 55, 71, 19, 216, 78, 125, 126, 142, 146, 114, 0 },
        Key{ 245, 110, 100, 66, 36, 244, 87, 100, 144, 207, 224, 222, 20, 36, 164, 83, 34, 18, 82, 155, 254, 55, 71, 19, 216, 78, 125, 126, 142, 146, 114, 1 },
        Key{ 245, 110, 100, 66, 36, 244, 87, 100, 144, 207, 224, 222, 20, 36, 164, 83, 34, 18, 82, 155, 254, 55, 71, 19, 216, 78, 125, 126, 142, 146, 114, 2 },
        Key{ 245, 110, 100, 66, 36, 244, 87, 100, 144, 207, 224, 222, 20, 36, 164, 83, 34, 18, 82, 155, 254, 55, 71, 19, 216, 78, 125, 126, 142, 146, 114, 3 },
        Key{ 245, 110, 100, 66, 36, 244, 87, 100, 144, 207, 224, 222, 20, 36, 164, 83, 34, 18, 82, 155, 254, 55, 71, 19, 216, 78, 125, 126, 142, 146, 114, 4 },
    };
    const test_account_values = [_]*const Slot{
        &Slot{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 },
        &Slot{ 0, 0, 100, 167, 179, 182, 224, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 },
        &Slot{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 },
        &Slot{ 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112 },
        &Slot{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 },
    };

    for (test_account_keys, 0..) |key, i| {
        try root.insert(key, test_account_values[i], testing.allocator, &crs);
    }

    const rust_root_comm = [_]u8{ 16, 237, 137, 216, 144, 71, 187, 22, 139, 170, 78, 105, 184, 96, 126, 38, 0, 73, 233, 40, 221, 188, 178, 253, 210, 62, 160, 244, 24, 43, 31, 138 };

    const r = try root.commitment();

    const r_bytes = r.toBytes();

    try std.testing.expectEqual(rust_root_comm, r_bytes);
}
