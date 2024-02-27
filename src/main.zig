const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const curve = std.crypto.ecc.Edwards25519;
const verkle_crypto = @import("verkle-crypto");
const banderwagon = verkle_crypto.banderwagon;
const Element = banderwagon.Element;
const Fr = banderwagon.Fr;
const CRS = verkle_crypto.crs.CRS;
const CRS_Domain = verkle_crypto.crs.Domain;
const copy = std.mem.copy;

const Slot = [32]u8;
const Key = [32]u8;
const Stem = [31]u8;
const Hash = [32]u8;

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
        try self.zis.appendSlice(other.zis.items);
        try self.yis.appendSlice(other.yis.items);
        try self.cis.appendSlice(other.cis.items);
        try self.esses.appendSlice(other.esses.items);
        try self.poas.appendSlice(other.poas.items);
        try self.values.appendSlice(other.values.items);
    }

    pub fn init(alloc: Allocator) Self {
        return Self{
            .cis = ArrayList(*Element).init(alloc),
            .yis = ArrayList(?Fr).init(alloc),
            .zis = ArrayList(u8).init(alloc),
            .esses = ArrayList(u8).init(alloc),
            .poas = ArrayList(Stem).init(alloc),
            .values = ArrayList(?*Slot).init(alloc),
        };
    }

    fn deinit(self: *ProofItems) void {
        self.cis.deinit();
        self.yis.deinit();
        self.zis.deinit();
        self.esses.deinit();
        self.poas.deinit();
        self.values.deinit();
    }
};

fn leafToFrs(fill: []Fr, val: ?*Slot) !void {
    if (val) |v| {
        _ = v;
        var lo = [_]u8{0} ** 16 ++ [_]u8{1} ++ [_]u8{0} ** 15;
        var hi = [_]u8{0} ** 32;
        std.mem.copy(u8, lo[0..16], val.?[0..16]);
        std.mem.copy(u8, hi[0..16], val.?[16..]);
        fill[0] = Fr.fromBytes(lo);
        fill[1] = Fr.fromBytes(hi);
    }
}

fn fillSuffixTreePoly(ret: *[256]Fr, values: []const ?*Slot) !usize {
    if (values.len != 128) {
        return error.InvalidValueSubGroupSize;
    }
    var count: usize = 0;
    for (values, 0..) |val, idx| {
        if (val != null) {
            count += 1;
            try leafToFrs(ret[(idx << 1) & 0xff ..], val);
        }
    }

    return count;
}

const LastLevelNode = struct {
    values: [256]?*Slot,
    stem: Stem,
    crs: *CRS,
    is_poa_stub: bool,
    c1: ?*Element,
    c2: ?*Element,
    depth: u8,

    fn computeSuffixNodeCommitment(crs: *CRS, values: []const ?*Slot) !Element {
        if (values.len != 128) {
            return error.InvalidValueArrayLength;
        }

        var vals: [256]Fr = undefined;
        for (values, 0..) |value, i| {
            if (value != null) {
                var data: [Fr.BytesSize]u8 = [_]u8{0} ** Fr.BytesSize;

                // lsb
                copy(u8, data[0..16], value.?[0..16]);
                data[16] = 1; // leaf marker
                vals[2 * i] = Fr.fromBytes(data);

                // msb
                copy(u8, data[0..16], value.?[16..]);
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
        std.mem.copy(u8, stem[0..], self.stem[0..31]);
        vals[1] = Fr.fromBytes(stem);

        const c1 = try computeSuffixNodeCommitment(self.crs, self.values[0..128]);
        const c2 = try computeSuffixNodeCommitment(self.crs, self.values[128..]);

        vals[2] = c1.mapToScalarField();
        vals[3] = c2.mapToScalarField();

        return self.crs.commit(vals[0..]);
    }

    fn getProofItems(self: *const LastLevelNode, keys: []const Key, alloc: Allocator) !ProofItems {
        var has_c1 = false;
        var has_c2 = false;
        var proof_items = ProofItems.init(alloc);
        errdefer proof_items.deinit();

        for (keys) |key| {
            if (std.mem.eql(u8, key[0..31], &self.stem)) {
                has_c1 = key[31] < 128;
                has_c2 = key[31] >= 128;
                if (has_c2) {
                    break;
                }
            }
        }

        if (self.is_poa_stub) {
            if (has_c1 or has_c2 or self.c1 != null or self.c2 != null) {
                return error.InvalidProofOfAbsenceStub;
            }
        }
        // else: batch map to scalar field when supported

        // serialize commitments if they are required
        if (has_c1) {
            try proof_items.cis.append(self.c1.?);
            try proof_items.zis.append(2);
            try proof_items.yis.append(Element.mapToScalarField(self.c1.?.*));
        }
        if (has_c2) {
            try proof_items.cis.append(self.c2.?);
            try proof_items.zis.append(3);
            try proof_items.yis.append(Element.mapToScalarField(self.c2.?.*));
        }

        // second pass: add the Cn-level elements
        for (keys) |key| {
            // another present stem proves the absence of this stem
            if (!std.mem.eql(u8, key[0..31], self.stem[0..])) {
                if (proof_items.esses.items.len == 0) {
                    try proof_items.poas.append(self.stem);
                    try proof_items.esses.append(@intFromEnum(ExtStatus.Other) | self.depth << 3);
                }
                try proof_items.values.append(null);
                continue;
            }

            // corner case: if a proof-of-absence stem was found, and the same stem is used as a proof-of-presence, clear the list.
            if (proof_items.poas.items.len > 0) {
                proof_items.poas.clearAndFree();
                proof_items.esses.clearAndFree();
            }
            const suffix = key[31];
            var suffix_poly: [256]Fr = [_]Fr{Fr.zero()} ** 256;
            var subrange_start: usize = 0;
            var subrange_end: usize = 128;
            if (suffix >= 128) {
                subrange_start = 128;
                subrange_end = 256;
            }
            const count = try fillSuffixTreePoly(&suffix_poly, self.values[subrange_start..subrange_end]);

            // proof of absence: case of a missing suffix tree.
            if (count == 0) {
                try proof_items.esses.append(@intFromEnum(ExtStatus.Empty) | self.depth << 3);
                try proof_items.values.append(null);
                continue;
            }

            // leaf is present
            var cn: *Element = undefined;
            if (suffix < 128) {
                cn = self.c1.?;
            } else {
                cn = self.c2.?;
            }
            try proof_items.cis.append(cn);
            try proof_items.cis.append(cn);
            try proof_items.zis.append(2 * suffix);
            try proof_items.zis.append(2 * suffix + 1);
            try proof_items.yis.append(suffix_poly[2 * suffix]);
            try proof_items.yis.append(suffix_poly[2 * suffix + 1]);
            try proof_items.values.append(self.values[suffix]);

            if (proof_items.esses.items.len == 0 or proof_items.esses.items[proof_items.esses.items.len - 1] != @intFromEnum(ExtStatus.Present) | self.depth << 3) {
                try proof_items.esses.append(@intFromEnum(ExtStatus.Present) | self.depth << 3);
            }
        }
        return proof_items;
    }
};

const BranchNode = struct {
    children: [256]Node,
    depth: u8,
    count: u8,
    crs: *CRS,

    fn computeCommitment(self: *const BranchNode) anyerror!Element {
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

    fn getProofItems(self: *const BranchNode, keys: []const Key, alloc: Allocator) !ProofItems {
        var groupstart: usize = 0;
        // TODO initialize with my proof info
        var proof_items = ProofItems.init(alloc);
        errdefer proof_items.deinit();

        while (groupstart < keys.len) {
            var groupend = groupstart;
            while (groupend < keys.len and keys[groupend][self.depth] == keys[groupstart][self.depth]) {
                groupend += 1;
            }

            const child_proof_items = try self.children[keys[groupstart][self.depth]].getProofItems(keys[groupstart..groupend], alloc);

            try proof_items.merge(&child_proof_items);
        }
        return proof_items;
    }
};

fn newll(key: Key, value: *const Slot, allocator: Allocator, crs: *CRS) !*LastLevelNode {
    const slot = key[31];
    var ll = try allocator.create(LastLevelNode);
    ll.values = [_]?*Slot{null} ** 256;
    ll.stem = [_]u8{0} ** 31;
    std.mem.copy(u8, ll.stem[0..], key[0..31]);
    ll.values[slot] = try allocator.create(Slot);
    std.mem.copy(u8, ll.values[slot].?[0..], value[0..]);
    ll.crs = crs;
    return ll;
}

const Node = union(enum) {
    last_level: *LastLevelNode,
    branch: *BranchNode,
    hash: Hash,

    empty: struct {},
    unresolved: struct {},

    fn new(allocator: Allocator, crs: *CRS) !@This() {
        var children: [256]Node = undefined;
        for (children, 0..) |_, idx| {
            children[idx] = Node{ .empty = .{} };
        }
        var br = try allocator.create(BranchNode);
        br.crs = crs;
        br.depth = 0;
        br.count = 0;
        br.children = children;
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
            .unresolved => error.ReadFromUnresolved,
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
                    std.mem.copy(u8, ll.values[key[31]].?[0..], value[0..]);
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
            .hash => {},
            .unresolved => {},
        }
    }

    fn commitment(self: *const Node) !Element {
        return switch (self.*) {
            .empty => Element.identity(),
            .hash => |_| error.NeedToReworkHashedNodes,
            .last_level => |ll| ll.computeCommitment(),
            .branch => |br| br.computeCommitment(),
            .unresolved => error.CannotComputeUnresolvedCommitment,
        };
    }

    // TODO remove allocator
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

    fn getProofItems(self: *const Node, keys: []const Key, alloc: Allocator) anyerror!ProofItems {
        return switch (self.*) {
            .branch => |br| br.getProofItems(keys, alloc),
            .last_level => |ll| ll.getProofItems(keys, alloc),
            else => error.NotImplemented,
        };
    }
};

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

    var br: *BranchNode = root.branch;
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
    var key1 = [_]u8{0} ** 32;
    var value1 = [_]u8{11} ** 32;
    try root.insert(key1, &value1, testing.allocator, &crs);
    var key2 = [1]u8{1} ++ [_]u8{0} ** 31;
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

test "get proof items for a tree with 3 values, 1 in each branch" {
    var crs = try CRS.init(testing.allocator);
    defer crs.deinit();
    var root_ = try Node.new(testing.allocator, &crs);
    var root = &root_;
    defer root.tear_down(testing.allocator);

    const keys = [_]Key{
        Key{ 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1 },
        Key{ 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2 },
        Key{ 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0 },
    };
    const values = [_]*const Slot{
        &Slot{ 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112 },
        &Slot{ 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112 },
        &Slot{ 197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112 },
    };

    for (keys, 0..) |key, i| {
        try root.insert(key, values[i], testing.allocator, &crs);
    }

    _ = try root.getProofItems(keys[0..1], testing.allocator);
}
