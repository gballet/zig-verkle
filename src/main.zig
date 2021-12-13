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
    children: [256]?Node,
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
                // Do not copy the value for now. This might cause some
                // heisenbugs in the future, as immutability isn't enforced.
                // It will do for now.
                ll.values[slot] = value;
                std.mem.copy(u8, ll.key[0..], key[0..31]);
                self.* = @unionInit(Node, "last_level", ll);
            },
            .hash => error.InsertIntoHash,
            .last_level => |ll| {
                // Check if the keys are the same, if so, then just place the value
                // in the corresponding slot, as the final extension tree has been
                // reached.
                const diffidx = std.mem.indexOfDiff(u8, ll.key[0..], key[0..31]);
                if (diffidx == null) {
                    ll.values[key[31]] = value;
                    return;
                }

                var br = try allocator.create(BranchNode);
                br.children = [_]?Node{null} ** 256;
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
                return br.children[key[br.depth]].?.insert_with_depth(key, value, allocator, depth + 1);
            },
            else => error.NodeTypeNotSupported,
        };
    }

    fn tear_down(self: *Node, allocator: *Allocator) void {
        switch (self.*) {
            .empty => {},
            .last_level => |ll| {
                // TODO need to check that this value has been
                // allocated on the heap and not on the stack.
                //for (ll.values) |v| {
                //if (v != null) {
                //allocator.free(v.?);
                //}
                //}

                allocator.destroy(ll);
            },
            .branch => |br| {
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
                if (i < 2) {
                    try testing.expect(child != null);
                    switch (child.?) {
                        Node.last_level => |ll| {
                            for (ll.values) |v, j| {
                                if (j == 0) {
                                    try testing.expect(v != null);
                                } else {
                                    try testing.expect(v == null);
                                }
                            }
                        },
                        else => return error.InvalidNodeType,
                    }
                } else {
                    try testing.expect(child == null);
                }
            }
        },
        else => return error.InvalidNodeType,
    }
}
