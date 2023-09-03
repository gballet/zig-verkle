const std = @import("std");
const Builder = std.build.Builder;

pub fn build(b: *Builder) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const lib = b.addStaticLibrary(.{
        .name = "verkle",
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(lib);

    var main_tests = b.addRunArtifact(b.addTest(.{
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    }));

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&main_tests.step);
}
