const std = @import("std");
const testing = std.testing;

const Slot = [32]u8;
const Key = [32]u8;
const Stem = [31]u8;
const Hash = [32]u8;

const Node = union(enum) {
    last_level: struct {
        values: Slot,
        key: Stem,
    },
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

    fn insert(self: *Node, key: Key, value: Slot, allocator: *std.mem.Allocator) !void {
        return switch (self.*) {
            .hash => error.InsertIntoHash,
            else => error.NodeTypeNotSupported,
        };
    }
};

test "inserting into hash raises an error" {
    var root = Node{ .hash = [_]u8{0} ** 32 };
    try testing.expectError(error.InsertIntoHash, root.insert([_]u8{0} ** 32, [_]u8{0} ** 32, testing.allocator));
}
