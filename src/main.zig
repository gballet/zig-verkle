const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

const Slot = [32]u8;
const Key = [32]u8;
const Stem = [31]u8;
const Hash = [32]u8;

const LastLevelNode = struct {
    values: [256]?*Slot,
    key: Stem,
};

const BranchNode = struct {
    children: [256]Node,
    depth: u8,
    count: u8,
};

const Node = union(enum) {
    last_level: *LastLevelNode,
    branch: *BranchNode,
    hash: Hash,

    empty: struct {},

    fn new() @This() {
        return @This(){ .empty = .{} };
    }

    fn insert(self: *Node, key: Key, value: *Slot, allocator: *Allocator) !void {
        return self.insert_with_depth(key, value, allocator, 0);
    }

    fn insert_with_depth(self: *Node, key: Key, value: *Slot, allocator: *Allocator, depth: u8) !void {
        return switch (self.*) {
            .empty => {
                const slot = key[31];
                var ll = try allocator.create(LastLevelNode);
                ll.values = [_]?*Slot{null} ** 256;
                ll.key = [_]u8{0} ** 31;
                std.mem.copy(u8, ll.key[0..], key[0..31]);
                ll.values[slot] = try allocator.create(Slot);
                std.mem.copy(u8, ll.values[slot].?[0..], value[0..]);
                self.* = @unionInit(Node, "last_level", ll);
            },
            .hash => error.InsertIntoHash,
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
                if (ll.key[br.depth] != key[br.depth]) {
                    var ll2 = try allocator.create(LastLevelNode);
                    ll2.key = [_]u8{0} ** 31;
                    std.mem.copy(u8, ll2.key[0..], key[0..31]);
                    ll2.values = [_]?*Slot{null} ** 256;
                    br.children[key[br.depth]] = Node{ .last_level = ll2 };
                }
                self.* = @unionInit(Node, "branch", br);
                return br.children[key[br.depth]].insert_with_depth(key, value, allocator, depth + 1);
            },
            else => error.NodeTypeNotSupported,
        };
    }

    fn tear_down(self: *Node, allocator: *Allocator) void {
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
                for (br.children) |_, i| {
                    br.children[i].tear_down(allocator);
                }

                allocator.destroy(br);
            },
            // TODO complete list
            else => @panic("unsupported node type in tear_down"),
        }
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
            for (ll.values) |v, i| {
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
            for (ll.values) |v, i| {
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
            for (br.children) |child, i| {
                switch (child) {
                    Node.last_level => |ll| {
                        try testing.expect(i < 2);
                        for (ll.values) |v, j| {
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
            for (br.children) |child, i| {
                if (i == 0) try testing.expect(child == .branch) else try testing.expect(child == .empty);
            }
            br = br.children[0].branch;
        } else if (br.depth == 30) {
            for (br.children) |child, i| {
                if (i < 2) try testing.expect(child == .last_level) else try testing.expect(child == .empty);
            }
            break;
        } else {
            try testing.expect(false);
        }
    }
}
