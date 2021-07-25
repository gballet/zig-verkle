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

const Node = union(enum) {
    last_level: LastLevelNode,
    branch: struct {
        children: [256]?*Node,
        depth: u8,
        count: u8,
    },
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
                var ll = LastLevelNode{
                    .values = [_]?*Slot{null} ** 256,
                    .key = [_]u8{0} ** 31,
                };
                // Do not copy the value for now. This might cause some
                // heisenbugs in the future, as immutability isn't enforced.
                // It will do for now.
                ll.values[slot] = value;
                std.mem.copy(u8, ll.key[0..], key[0..31]);
                self.* = @unionInit(Node, "last_level", ll);
            },
            else => error.NodeTypeNotSupported,
        };
    }
};

test "inserting into hash raises an error" {
    var root = Node{ .hash = [_]u8{0} ** 32 };
    var value = [_]u8{0} ** 32;
    try testing.expectError(error.InsertIntoHash, root.insert([_]u8{0} ** 32, &value, testing.allocator));
}

test "insert into empty tree" {
    var root = Node.new();
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);

    switch (root) {
        Node.last_level => |*ll| {
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
