const std = @import("std");
const Build = std.Build;

pub fn build(b: *Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const verkle_crypto = b.dependency("verkle-crypto", .{
        .target = target,
        .optimize = optimize,
    });

    const lib = b.addStaticLibrary(.{
        .name = "verkle",
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(lib);

    const to_dot_exe = b.addExecutable(.{
        .name = "to_dot",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    to_dot_exe.root_module.addImport("verkle-crypto", verkle_crypto.module("verkle-crypto"));
    // to_dot_exe.linkLibrary(verkle_crypto.artifact("verkle-crypto"));
    var to_dot = b.addRunArtifact(to_dot_exe);
    const to_dot_step = b.step("todot", "Dump dot file");
    to_dot_step.dependOn(&to_dot.step);

    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    unit_tests.root_module.addImport("verkle-crypto", verkle_crypto.module("verkle-crypto"));
    var main_tests = b.addRunArtifact(unit_tests);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&main_tests.step);
}
