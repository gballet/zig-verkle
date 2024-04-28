const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const curve = std.crypto.ecc.Edwards25519;
const verkle_crypto = @import("verkle-crypto");
const banderwagon = verkle_crypto.banderwagon;
const Element = banderwagon.Element;
const Fr = banderwagon.Fr;
const CRS = verkle_crypto.crs.CRS;
const CRS_Domain = verkle_crypto.crs.Domain;
const copy = std.mem.copy;
const types = @import("./types.zig");

const Slot = types.Slot;
const Stem = types.Stem;
const Key = types.Key;
const Hash = types.Hash;

pub const ExtStatus = enum {
    Empty,
    Other,
    Present,
};

pub const ProofItems = struct {
    cis: ArrayList(*Element),
    yis: ArrayList(?Fr),
    zis: ArrayList(u8),
    // don't support stateful proofs just yet
    // fis: *ArrayList(ArrayList(*Fr)),

    esses: ArrayList(u8),
    poas: ArrayList(Stem),
    values: ArrayList(?*Slot),

    const Self = @This();

    fn merge(self: *ProofItems, other: *const ProofItems) !void {
        _ = other;
        _ = self;
    }
};
