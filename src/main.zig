const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;
// Use Edwards25519 at the moment, since bandersnatch is currently
// unavailable, and Edwards is the only curve available in zig, that
// both supports addition and serializes to 32 bytes.
const curve = std.crypto.ecc.Edwards25519;

const Slot = [32]u8;
const Key = [32]u8;
const Stem = [31]u8;
const Hash = [32]u8;

fn generateInsecure(comptime n: usize) ![n]curve {
    var r: [n]curve = undefined;
    var i: usize = 0;
    var v: [32]u8 = undefined;
    while (i < n) : (i += 1) {
        std.mem.writeIntSliceBig(usize, v[0..], i + 2);
        r[i] = try curve.mul(curve.basePoint, v);
    }

    return r;
}

const ProofItems = struct {
    fn merge(self: *ProofItems, other: *const ProofItems) !void {
        _ = other;
        _ = self;
    }
};

const LastLevelNode = struct {
    values: [256]?*Slot,
    key: Stem,

    fn computeSuffixNodeCommitment(srs: [256]curve, values: []const ?*Slot) !Hash {
        var multiplier = [_]u8{0} ** 32;
        var i: usize = 0;
        var ret = curve.identityElement;
        while (i < values.len) : (i += 1) {
            if (values[i] != null) {
                std.mem.copy(u8, multiplier[16..], values[i].?[0..16]);
                multiplier[15] = 1; // set the leaf marker
                ret = curve.add(ret, try curve.mul(srs[2 * i], multiplier));
                multiplier[15] = 0; // clear the leaf marker
                // Multiplying by 0 will give the identity element, and
                // the Edwards25519 won't allow this result. Since it's
                // a no-op anyway, skip it.
                for (multiplier[16..]) |v| {
                    if (v != 0) {
                        std.mem.copy(u8, multiplier[16..], values[i].?[16..]);
                        ret = curve.add(ret, try curve.mul(srs[2 * i + 1], multiplier));
                    }
                }
            }
        }

        return ret.toBytes();
    }

    fn isZero(stem: []const u8) bool {
        for (stem) |v| {
            if (v != 0)
                return false;
        }

        return true;
    }

    fn computeCommitment(self: *const LastLevelNode) !Hash {
        // TODO find a way to generate this at compile/startup
        // time, without running into the 1000 backwards branches
        // issue.
        const srs = try generateInsecure(256);
        const c1 = try computeSuffixNodeCommitment(srs, self.values[0..128]);
        const c2 = try computeSuffixNodeCommitment(srs, self.values[128..]);
        var stem = [_]u8{0} ** 32;
        std.mem.copy(u8, stem[1..], self.key[0..]);
        var res = curve.add(try curve.mul(srs[2], c1), try curve.mul(srs[3], c2));
        res = curve.add(res, srs[0]);
        if (!isZero(stem[0..])) {
            res = curve.add(res, try curve.mul(srs[1], stem));
        }
        return res.toBytes();
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

    fn computeCommitment(self: *const BranchNode) anyerror!Hash {
        // TODO find a way to generate this at compile/startup
        // time, without running into the 1000 backwards branches
        // issue.
        const srs = try generateInsecure(256);
        var res = curve.identityElement;
        for (self.children, 0..) |child, i| {
            if (child != .empty) {
                res = curve.add(res, try curve.mul(srs[i], try child.commitment()));
            }
        }
        return res.toBytes();
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

fn newll(key: Key, value: *Slot, allocator: Allocator) !*LastLevelNode {
    const slot = key[31];
    var ll = try allocator.create(LastLevelNode);
    ll.values = [_]?*Slot{null} ** 256;
    ll.key = [_]u8{0} ** 31;
    std.mem.copy(u8, ll.key[0..], key[0..31]);
    ll.values[slot] = try allocator.create(Slot);
    std.mem.copy(u8, ll.values[slot].?[0..], value[0..]);
    return ll;
}

const Node = union(enum) {
    last_level: *LastLevelNode,
    branch: *BranchNode,
    hash: Hash,

    empty: struct {},
    unresolved: struct {},

    fn new() @This() {
        return @This(){ .empty = .{} };
    }

    fn insert(self: *Node, key: Key, value: *Slot, allocator: Allocator) !void {
        return self.insert_with_depth(key, value, allocator, 0);
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

    fn insert_with_depth(self: *Node, key: Key, value: *Slot, allocator: Allocator, depth: u8) anyerror!void {
        return switch (self.*) {
            .empty => {
                self.* = @unionInit(Node, "last_level", try newll(key, value, allocator));
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
                self.* = @unionInit(Node, "branch", br);
                // Recurse into the child, if this is empty then it will be turned
                // into a last_level node in the recursing .empty case, and if the
                // next byte in the key are the same, it will recurse into another
                // .last_level case, potentially doing so over the whole stem.
                return br.children[key[br.depth]].insert_with_depth(key, value, allocator, depth + 1);
            },
            .branch => |br| br.children[key[br.depth]].insert(key, value, allocator),
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

    fn commitment(self: *const Node) !Hash {
        return switch (self.*) {
            .empty => [_]u8{0} ** 32,
            .hash => |h| h,
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
};

test "inserting into hash raises an error" {
    var root_ = Node{ .hash = [_]u8{0} ** 32 };
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try testing.expectError(error.InsertIntoHash, root.insert([_]u8{0} ** 32, &value, testing.allocator));
}

test "insert into empty tree" {
    var root_ = Node.new();
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    defer root.tear_down(testing.allocator);

    switch (root.*) {
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
    }
}

test "insert into a last_level node, difference in suffix" {
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    try root.insert([_]u8{0} ** 31 ++ [1]u8{1}, &value, testing.allocator);
    defer root.tear_down(testing.allocator);

    switch (root.*) {
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
    }
}

test "insert into a last_level node, difference in stem" {
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    try root.insert([1]u8{1} ++ [_]u8{0} ** 31, &value, testing.allocator);
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
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    try root.insert([_]u8{0} ** 30 ++ [2]u8{ 1, 0 }, &value, testing.allocator);
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
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    try root.insert([1]u8{1} ++ [_]u8{0} ** 31, &value, testing.allocator);
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
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{1} ** 32, &value, testing.allocator);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "compute root commitment of a last_level node, with 0 key" {
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "compute root commitment of a branch node" {
    var root_ = Node.new();
    var root = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);
    try root.insert([_]u8{1} ** 32, &value, testing.allocator);
    defer root.tear_down(testing.allocator);
    _ = try root.commitment();
}

test "get inserted value from a tree" {
    var root_ = Node.new();
    var root = &root_;
    var key1 = [_]u8{0} ** 32;
    var value1 = [_]u8{11} ** 32;
    try root.insert(key1, &value1, testing.allocator);
    var key2 = [1]u8{1} ++ [_]u8{0} ** 31;
    var value2 = [_]u8{22} ** 32;
    try root.insert(key2, &value2, testing.allocator);
    defer root.tear_down(testing.allocator);

    var val = try root.get(key1);
    _ = try testing.expect(val != null);
    _ = try testing.expect(std.mem.eql(u8, val.?, &value1));
    val = try root.get(key2);
    _ = try testing.expect(val != null);
    _ = try testing.expect(std.mem.eql(u8, val.?, &value2));
}

test "check verkle-crypto can be imported" {
    const verkle_crypto = @import("verkle-crypto");
    const banderwagon = verkle_crypto.banderwagon;
    const Element = banderwagon.Element;
    const expect = testing.expect;

    var point = Element.generator();

    try expect(Element.equal(point, Element.generator()));

    Element.double(&point, point);

    try expect(!Element.equal(point, Element.generator()));
}
