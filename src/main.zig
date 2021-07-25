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

    fn destroy(self: *Node, allocator: *Allocator) void {
        switch (self.*) {
            else => {}, // unsupported node type
        }
    }

    fn insert(self: *Node, key: Key, value: *Slot, allocator: *Allocator) !void {
        return switch (self.*) {
            .hash => error.InsertIntoHash,
            .empty => |*llo| {
                const slot = key[31];
                var ll = try allocator.create(LastLevelNode);
                errdefer allocator.destroy(ll);
                // Do not copy the value for now. This might cause some
                // heisenbugs in the future, as immutability isn't enforced.
                // It will do for now.
                ll.values[slot] = value;
                std.mem.copy(u8, ll.key[0..], key[0..31]);
                self.* = @unionInit(Node, "last_level", ll.*);
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
    defer root.destroy(testing.allocator);
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, testing.allocator);

    switch (root) {
        Node.last_level => {},
        else => return error.InvalidNodeType,
    }
}
