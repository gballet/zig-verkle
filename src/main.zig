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
    children: [256]?*Node,
    depth: u8,
    count: u8,
};

const Node = union(enum) {
    last_level: *LastLevelNode,
    branch: *BranchNode,
    hash: Hash,
    empty: ?bool,

    fn new() @This() {
        return @This(){ .empty = null };
    }

    fn insert(self: *Node, key: Key, value: *Slot, allocator: *Allocator) !void {
        return switch (self.*) {
            .hash => error.InsertIntoHash,
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
            .last_level => |ll| {
                const diffidx = std.mem.indexOfDiff(u8, ll.key[0..], key[0..31]);
                var br = try allocator.create(BranchNode);
                br.children = [_]?*Node{null} ** 256;
                br.depth = 0;
                br.count = 2;
                self.* = @unionInit(Node, "branch", br);
            },
            else => error.NodeTypeNotSupported,
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
    var root_ = Node{ .empty = .{} };
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);

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
