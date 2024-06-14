const std = @import("std");
const verkle_crypto = @import("verkle-crypto");
const CRS = verkle_crypto.crs.CRS;
const verklelib = @import("./lib.zig");

const Node = verklelib.Node;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer {
        _ = gpa.deinit();
    }

    var crs = try CRS.init(gpa.allocator());
    defer crs.deinit();

    var root_ = try Node.new(gpa.allocator(), &crs);
    var root: *Node = &root_;
    var value = [_]u8{0} ** 32;
    try root.insert([_]u8{0} ** 32, &value, gpa.allocator(), &crs);
    defer root.tear_down(gpa.allocator());
    var list = std.ArrayList(u8).init(gpa.allocator());
    defer list.deinit();

    try root.toDot(&list, "", "");
    std.debug.print("{s}\n", .{list.items[0..]});
}
