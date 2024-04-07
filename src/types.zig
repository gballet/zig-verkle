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

pub const Slot = [32]u8;
pub const Key = [32]u8;
pub const Stem = [31]u8;
pub const Hash = [32]u8;
