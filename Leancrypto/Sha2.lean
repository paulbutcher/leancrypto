/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
SHA-256, SHA-384 and SHA-512 (FIPS 180-4), and a selector naming one of them.

Written against the published test vectors rather than proved: the round function is arithmetic
on machine words with no structure a proof could exploit, and a golden vector catches every
transcription error the code can contain.

The 256 and 512 families share their shape and nothing else: different word width, round count,
initial values, constants, rotations, block size and length field. Written out twice for that
reason, rather than abstracted over a width the two do not actually share.
-/

public section

namespace Leancrypto.Sha256

private def roundConstants : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotation counts in SHA-256 are always between 1 and 31, so the complementary shift is never
a whole word. -/
private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def word (bytes : Array UInt8) (offset : Nat) : UInt32 :=
  ((bytes.getD offset 0).toUInt32 <<< 24) ||| ((bytes.getD (offset + 1) 0).toUInt32 <<< 16) |||
    ((bytes.getD (offset + 2) 0).toUInt32 <<< 8) ||| (bytes.getD (offset + 3) 0).toUInt32

/-- Appends the terminator, the zero fill, and the message length in bits as a big-endian
64-bit count. -/
private def pad (message : Array UInt8) : Array UInt8 := Id.run do
  let bitLength : UInt64 := (UInt64.ofNat message.size) * 8
  let afterTerminator := message.size + 1
  let zeros := (56 + 64 - afterTerminator % 64) % 64
  let mut padded := message.push 0x80
  for _ in [0:zeros] do
    padded := padded.push 0
  for shift in [0:8] do
    padded := padded.push (bitLength >>> (UInt64.ofNat ((7 - shift) * 8))).toUInt8
  pure padded

private def schedule (chunk : Array UInt8) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (word chunk (i * 4))
  for i in [16:64] do
    let previous := w.getD (i - 15) 0
    let recent := w.getD (i - 2) 0
    let s0 := rotr previous 7 ^^^ rotr previous 18 ^^^ (previous >>> 3)
    let s1 := rotr recent 17 ^^^ rotr recent 19 ^^^ (recent >>> 10)
    w := w.push (w.getD (i - 16) 0 + s0 + w.getD (i - 7) 0 + s1)
  pure w

private def compress (state : Array UInt32) (chunk : Array UInt8) : Array UInt32 := Id.run do
  let w := schedule chunk
  let mut a := state.getD 0 0
  let mut b := state.getD 1 0
  let mut c := state.getD 2 0
  let mut d := state.getD 3 0
  let mut e := state.getD 4 0
  let mut f := state.getD 5 0
  let mut g := state.getD 6 0
  let mut h := state.getD 7 0
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let choice := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + s1 + choice + roundConstants.getD i 0 + w.getD i 0
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + majority
    h := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  pure #[state.getD 0 0 + a, state.getD 1 0 + b, state.getD 2 0 + c, state.getD 3 0 + d,
    state.getD 4 0 + e, state.getD 5 0 + f, state.getD 6 0 + g, state.getD 7 0 + h]

private def hashArray (message : Array UInt8) : Array UInt8 := Id.run do
  let padded := pad message
  let mut state := initialState
  for chunk in [0:padded.size / 64] do
    state := compress state (padded.extract (chunk * 64) (chunk * 64 + 64))
  let mut digest : Array UInt8 := Array.emptyWithCapacity 32
  for value in state do
    for shift in [0:4] do
      digest := digest.push (value >>> (UInt32.ofNat ((3 - shift) * 8))).toUInt8
  pure digest

def hash (message : ByteArray) : ByteArray := ⟨hashArray message.data⟩

/-- The bytes hashed are the UTF-8 encoding. A hash of a string is a hash of an encoding of it,
and a caller who does not know which encoding has a bug waiting. -/
def hashUtf8 (message : String) : ByteArray := hash message.toUTF8

end Leancrypto.Sha256

namespace Leancrypto.Sha512

private def roundConstants : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

private def initialState : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- SHA-384 is SHA-512 under different initial values, truncated. Truncation alone would leave
the discarded words recoverable as a length extension over the whole state, so the standard
changes the starting point too. -/
private def initialState384 : Array UInt64 :=
  #[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- Rotation counts in SHA-512 are always between 1 and 63, so the complementary shift is never
a whole word. -/
private def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

private def word (bytes : Array UInt8) (offset : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for index in [0:8] do
    value := (value <<< 8) ||| (bytes.getD (offset + index) 0).toUInt64
  pure value

/-- Appends the terminator, the zero fill, and the message length in bits as a big-endian
128-bit count. Eight bytes address every length an `Array UInt8` can have, so the count is
computed in 64 bits and written behind eight zeros rather than in a width nothing can reach. -/
private def pad (message : Array UInt8) : Array UInt8 := Id.run do
  let bitLength : UInt64 := (UInt64.ofNat message.size) * 8
  let afterTerminator := message.size + 1
  let zeros := (112 + 128 - afterTerminator % 128) % 128
  let mut padded := message.push 0x80
  for _ in [0:zeros + 8] do
    padded := padded.push 0
  for shift in [0:8] do
    padded := padded.push (bitLength >>> (UInt64.ofNat ((7 - shift) * 8))).toUInt8
  pure padded

private def schedule (chunk : Array UInt8) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.emptyWithCapacity 80
  for i in [0:16] do
    w := w.push (word chunk (i * 8))
  for i in [16:80] do
    let previous := w.getD (i - 15) 0
    let recent := w.getD (i - 2) 0
    let s0 := rotr previous 1 ^^^ rotr previous 8 ^^^ (previous >>> 7)
    let s1 := rotr recent 19 ^^^ rotr recent 61 ^^^ (recent >>> 6)
    w := w.push (w.getD (i - 16) 0 + s0 + w.getD (i - 7) 0 + s1)
  pure w

private def compress (state : Array UInt64) (chunk : Array UInt8) : Array UInt64 := Id.run do
  let w := schedule chunk
  let mut a := state.getD 0 0
  let mut b := state.getD 1 0
  let mut c := state.getD 2 0
  let mut d := state.getD 3 0
  let mut e := state.getD 4 0
  let mut f := state.getD 5 0
  let mut g := state.getD 6 0
  let mut h := state.getD 7 0
  for i in [0:80] do
    let s1 := rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41
    let choice := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + s1 + choice + roundConstants.getD i 0 + w.getD i 0
    let s0 := rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + majority
    h := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  pure #[state.getD 0 0 + a, state.getD 1 0 + b, state.getD 2 0 + c, state.getD 3 0 + d,
    state.getD 4 0 + e, state.getD 5 0 + f, state.getD 6 0 + g, state.getD 7 0 + h]

private def digest (initial : Array UInt64) (words : Nat) (message : ByteArray) : ByteArray :=
  Id.run do
    let padded := pad message.data
    let mut state := initial
    for chunk in [0:padded.size / 128] do
      state := compress state (padded.extract (chunk * 128) (chunk * 128 + 128))
    let mut output : Array UInt8 := Array.emptyWithCapacity (words * 8)
    for value in state.extract 0 words do
      for shift in [0:8] do
        output := output.push (value >>> (UInt64.ofNat ((7 - shift) * 8))).toUInt8
    pure ⟨output⟩

def hash (message : ByteArray) : ByteArray := digest initialState 8 message

/-- The bytes hashed are the UTF-8 encoding. A hash of a string is a hash of an encoding of it,
and a caller who does not know which encoding has a bug waiting. -/
def hashUtf8 (message : String) : ByteArray := hash message.toUTF8

end Leancrypto.Sha512

namespace Leancrypto.Sha384

def hash (message : ByteArray) : ByteArray := Sha512.digest Sha512.initialState384 6 message

/-- The bytes hashed are the UTF-8 encoding. A hash of a string is a hash of an encoding of it,
and a caller who does not know which encoding has a bug waiting. -/
def hashUtf8 (message : String) : ByteArray := hash message.toUTF8

end Leancrypto.Sha384

namespace Leancrypto

/-- Which member of the family a caller means, where something else is parametric in it. An
enumeration rather than a record of functions, so that a consumer needing one more thing per
digest, the `DigestInfo` prefix `Leancrypto.Rsa` selects for instance, can add it where that
thing belongs instead of here. -/
inductive Sha2 where
  | sha256
  | sha384
  | sha512
  deriving Repr, DecidableEq

def Sha2.hash : Sha2 → ByteArray → ByteArray
  | .sha256 => Sha256.hash
  | .sha384 => Sha384.hash
  | .sha512 => Sha512.hash

/-- The digest length in bytes. That this agrees with `hash` is checked by the vectors, which
compare the whole digest; no theorem here states it. -/
def Sha2.size : Sha2 → Nat
  | .sha256 => 32
  | .sha384 => 48
  | .sha512 => 64

/-- The compression block in bytes, which HMAC pads its key to. The 384 and 512 digests share a
block twice the width of the 256 one, so this is not a constant and nothing may treat it as one. -/
def Sha2.blockSize : Sha2 → Nat
  | .sha256 => 64
  | .sha384 => 128
  | .sha512 => 128

def Sha2.hashUtf8 (digest : Sha2) (message : String) : ByteArray :=
  digest.hash message.toUTF8

end Leancrypto
