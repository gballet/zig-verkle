const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;
// Use Edwards25519 at the moment, since bandersnatch is currently
// unavailable, and Edwards is the only curve available in zig, that
// both supports addition and serializes to 32 bytes.
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

const ProofItems = struct {
    fn merge(self: *ProofItems, other: *const ProofItems) !void {
        _ = other;
        _ = self;
    }
};

const LastLevelNode = struct {
    values: [256]?*Slot,
    key: Stem,
    crs: *CRS,

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
        std.mem.copy(u8, stem[0..], self.key[0..31]);
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
        var proof_items = ProofItems{};
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

    fn get_proof_items(self: *const BranchNode, keys: []Key) !ProofItems {
        var groupstart = 0;
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
    ll.key = [_]u8{0} ** 31;
    std.mem.copy(u8, ll.key[0..], key[0..31]);
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
                if (!std.mem.eql(u8, key[0..31], ll.key[0..31])) {
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
                const diffidx = std.mem.indexOfDiff(u8, ll.key[0..], key[0..31]);
                if (diffidx == null) {
                    ll.values[key[31]] = try allocator.create(Slot);
                    std.mem.copy(u8, ll.values[key[31]].?[0..], value[0..]);
                    return;
                }

                var br = try allocator.create(BranchNode);
                br.children = [_]Node{Node{ .empty = .{} }} ** 256;
                br.depth = depth;
                br.count = 2;
                br.children[ll.key[br.depth]] = Node{ .last_level = ll };
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

    // assume that keys are sorted
    fn get_proof_items(self: *const Node, keys: [][32]u8) !ProofItems {
        return switch (self.*) {
            .branch => |br| br.get_proof_items(keys),
            .last_level => |ll| ll.get_proof_items(keys),
            _ => error.NotImplemented,
        };
    }

    fn toDot(self: *const Node, str: *std.ArrayList(u8), allocator: Allocator, path: []const u8, parent: []const u8) !void {
        const comm = try self.commitment();
        const hash = comm.mapToScalarField().toBytes();
        const me = try std.fmt.allocPrint(allocator, "{s}{s}", .{ @tagName(self.*), path });
        defer allocator.free(me);
        switch (self.*) {
            .branch => |br| {
                if (br.depth == 0) {
                    _ = try str.writer().write("digraph D {\n");
                }

                try std.fmt.format(str.writer(), "{s} [label=\"I: {s}\"]\n", .{ me, hash });

                for (br.children, 0..) |child, childidx| {
                    if (child != .empty) {
                        const child_path = try std.fmt.allocPrint(allocator, "{s}{x:0>2}", .{ path, childidx });
                        defer allocator.free(child_path); // TODO reuse a buffer instead of allocating

                        try child.toDot(str, allocator, child_path, me);
                    }
                }

                if (br.depth == 0) {
                    _ = try str.writer().write("}");
                }
            },
            .last_level => |ll| {
                try std.fmt.format(str.writer(), "{s} [label=\"I: {s}\\nS: {s}\"]\n", .{ me, hash, ll.key });

                for (ll.values, 0..) |val, validx| {
                    if (val) |value| {
                        try std.fmt.format(str.writer(), "value{s}{x:0>2} [label=\"{s}\"]\n{s} -> value{s}{x:0>2}\n", .{ path, validx, value.*, me, path, validx });
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

    try root.toDot(&list, testing.allocator, "", "");
    std.debug.print("{s}\n", .{list.items[0..]});
}
//     var crs = try CRS.init(testing.allocator);
//     defer crs.deinit();
//     var root_ = try Node.new(testing.allocator, &crs);
//     var root: *Node = &root_;
//     var value = [_]u8{0} ** 32;
//     try root.insert([_]u8{0} ** 32, &value, testing.allocator, &crs);
//     defer root.tear_down(testing.allocator);

//     std.debug.print("{s}\n", .{try root.toDot(testing.allocator, "", "")});
// }

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
