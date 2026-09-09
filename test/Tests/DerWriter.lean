/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Hex
import Leancrypto.Der

/-!
The DER writer: what it puts on the wire, and that the reader beside it reads back what it wrote.

The round trip is a property rather than a theorem. Stating it is easy and proving it is not: the
reader works by index into a whole `ByteArray` under a limit, so a theorem would need a lemma
placing every nested structure's offset inside the concatenation the writer builds, for a modulus
whose width is a variable. That is a great deal of index arithmetic for a claim the checks below
already make over every shape of key the encoding distinguishes. What is proved instead is the part
that carries the meaning: that the digits the writer emits denote the number it was given, and that
they carry no leading zero, which is the whole of what DER requires of an integer's body.

A round trip alone would not catch a writer and a reader that agreed on a wrong encoding, so the
bytes are pinned twice over: against the octet-level rules of X.690 at the boundaries where the
short and long forms meet, and against the `SubjectPublicKeyInfo` OpenSSL writes for a real key.
-/

namespace Tests.DerWriter
open Leancrypto Leancrypto.Der

private theorem base256_lt {n : Nat} (h : n < 256) : base256 n = [UInt8.ofNat n] := by
  rw [base256.eq_def]; simp [h]

private theorem base256_ge {n : Nat} (h : ¬ n < 256) :
    base256 n = base256 (n / 256) ++ [UInt8.ofNat (n % 256)] := by
  rw [base256.eq_def]; simp [h]

/--
The digits the writer emits for a number are read back as that number. This is half of what makes
the writer correct, and the half a round trip against the reader could not distinguish from a
shared mistake: it is stated against `Rsa.natOfBytes`, which is what the rest of the library uses
to turn a big-endian octet string into a value, rather than against anything defined here.

`base256 n` is the writer's digits, `.toArray` makes them a `ByteArray`, and `Rsa.natOfBytes` folds
them big-endian; the equation says the fold gives `n` back, for every `n` including zero. The
induction is over `base256.induct`, so the two cases are the writer's own: a value below 256, which
is one digit, and a larger one, which is its quotient's digits followed by the remainder.
-/
theorem natOfBytes_base256 (n : Nat) : Rsa.natOfBytes ⟨(base256 n).toArray⟩ = n := by
  simp only [Rsa.natOfBytes, List.foldl_toArray]
  induction n using base256.induct with
  | case1 n _ =>
    rename_i h
    have hlt : n < 256 := h
    rw [base256_lt hlt]
    simp [Nat.mod_eq_of_lt hlt]
  | case2 n _ ih0 =>
    rename_i hy
    have hlt : ¬ n < 256 := hy
    have ih : List.foldl (fun acc (byte : UInt8) => acc * 256 + byte.toNat) 0
        (base256 (n / 256)) = n / 256 := ih0
    rw [base256_ge hlt]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, show (UInt8.ofNat (n % 256)).toNat = n % 256 by simp]
    omega

/--
The digits carry no leading zero. This is the other half: DER admits one spelling of an integer and
the reader refuses the rest, so a writer that padded on the left would produce a structure its own
reader rejects, and one that padded on the right would produce a different number.

The disjunction is how the claim is true at zero, where the single digit is a zero and has to be:
for every other `n` the first digit is non-zero. `head?` is `none` only for an empty list, which
`base256` never returns, so `getD 0` reads the first digit rather than standing in for a missing
one. The induction is over `base256.induct`, and the step turns on the first digit of a number's
digits being the first digit of its quotient's.
-/
theorem base256_head (n : Nat) : (base256 n).head?.getD 0 ≠ 0 ∨ n = 0 := by
  induction n using base256.induct with
  | case1 n _ =>
    rename_i hy
    have hlt : n < 256 := hy
    rw [base256_lt hlt]
    simp only [List.head?_cons, Option.getD_some, ne_eq]
    by_cases hzero : n = 0
    · exact Or.inr hzero
    · exact Or.inl fun hz =>
        hzero (by simpa [Nat.mod_eq_of_lt hlt] using congrArg UInt8.toNat hz)
  | case2 n _ ih0 =>
    rename_i hy
    have hlt : ¬ n < 256 := hy
    have ih : (base256 (n / 256)).head?.getD 0 ≠ 0 ∨ n / 256 = 0 := ih0
    have hi : (base256 (n / 256)).head?.getD 0 ≠ 0 := ih.resolve_right (by omega)
    rw [base256_ge hlt, List.head?_append]
    cases hb : (base256 (n / 256)).head? with
    | none => rw [hb] at hi; simp at hi
    | some b => rw [hb] at hi; exact Or.inl (by simpa using hi)

private def hex (bytes : ByteArray) : String := Codec.Hex.encodeString bytes

private def bytesOfHex (s : String) : ByteArray := (Codec.Hex.decodeString s).getD ⟨#[]⟩

/-- Bytes that vary rather than repeat, so that a width is filled with something other than a run
of one value. Nothing here needs them to be unpredictable; the offset keeps the first byte of each
width away from zero, so the modulus really has the width it is built for. -/
private def varyingByte (index : Nat) : Nat := (index * 1103515245 + 12345) % 251 + 5

private def varying (width : Nat) : Nat :=
  (List.range width).foldl (fun acc index => acc * 256 + varyingByte (index + width)) 0

/-- Four moduli per width: the largest value of that width, whose first octet is `0xff` and so
needs the sign octet in front of it; the smallest whose first octet still has its high bit set; the
largest whose first octet does not, which must not get one; and one whose octets vary. -/
private def moduli (width : Nat) : List Nat :=
  [256 ^ width - 1, 256 ^ width / 2, 256 ^ width / 2 - 1, varying width]

private def exponents : List Nat := [3, 17, 65537, 0x49d2a1, 256 ^ 5 - 1]

/-- The widths at which something changes: the short form of a length gives way to one octet, then
to two, and the modulus's own first octet crosses the sign bit at each of them. -/
private def widths : List Nat :=
  [1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 33, 63, 64, 65, 120, 126, 127, 128, 129, 130,
    192, 254, 255, 256, 257, 300, 384, 512]

private def readsBack (width : Nat) : Bool :=
  (moduli width).all fun modulus =>
    exponents.all fun exponent =>
      let key : Rsa.PublicKey := { modulus, exponent }
      publicKeyOfSpki (rsaPublicKeyInfo key) == some key

private def modulus : String :=
  "b8aeffb5f630b15119bc600828180769e0b432f0ef3d2f9e9aa6fe36a4c3fdc3" ++
  "973eb2a9e5a5c919b6eea2c39f9e2ca618a48cbefa0a5f8323dc960051ebfb3d" ++
  "cf84d726d10a01550b2baa57871c679987c70a35ee654734f22164153fe9e734" ++
  "e77de4ffcfcdc220f7469f601633d095d026a1c904315ce04e5048592957c3c9" ++
  "9a071633f1ffbff4f87c47ca05ef1d0858a48334c9799a9bf260f215df00d2b1" ++
  "548889835b23e202c24c9f9862add280b7aa5a99130a5a03d24ab0acf42c7387" ++
  "7edeaf5dcbdee2fb4bec385253163dfe3034126bfc8feefc883177103afb0ca9" ++
  "6afe212e5fba3f1ce155f9bf0ced6eba9e79a4d6c9399c1886553c3f65666035"

private def rsaSpki : String :=
  "30820122300d06092a864886f70d01010105000382010f003082010a02820101" ++
  "00b8aeffb5f630b15119bc600828180769e0b432f0ef3d2f9e9aa6fe36a4c3fd" ++
  "c3973eb2a9e5a5c919b6eea2c39f9e2ca618a48cbefa0a5f8323dc960051ebfb" ++
  "3dcf84d726d10a01550b2baa57871c679987c70a35ee654734f22164153fe9e7" ++
  "34e77de4ffcfcdc220f7469f601633d095d026a1c904315ce04e5048592957c3" ++
  "c99a071633f1ffbff4f87c47ca05ef1d0858a48334c9799a9bf260f215df00d2" ++
  "b1548889835b23e202c24c9f9862add280b7aa5a99130a5a03d24ab0acf42c73" ++
  "877edeaf5dcbdee2fb4bec385253163dfe3034126bfc8feefc883177103afb0c" ++
  "a96afe212e5fba3f1ce155f9bf0ced6eba9e79a4d6c9399c1886553c3f656660" ++
  "350203010001"

private def ecPoint : String :=
  "04d3cefdd1c5e74d8f9adc4749be372a188891065819c606fb97950c1de95fc2" ++
  "6cf67a8ec0bcb47d266213ff406168f3e2c661fd2b02b937e425b11bf6aa72ff" ++
  "99"

private def ecSpki : String :=
  "3059301306072a8648ce3d020106082a8648ce3d03010703420004d3cefdd1c5" ++
  "e74d8f9adc4749be372a188891065819c606fb97950c1de95fc26cf67a8ec0bc" ++
  "b47d266213ff406168f3e2c661fd2b02b937e425b11bf6aa72ff99"

private def rsaKey : Rsa.PublicKey :=
  { modulus := Rsa.natOfBytes (bytesOfHex modulus), exponent := 65537 }

public def checks : List (String × Bool) :=
  widths.map (fun width =>
      (s!"a key with a {width}-byte modulus is read back as it was written", readsBack width))
    ++ [ ("an INTEGER takes the fewest octets that keep it positive",
          hex (integer 0) == "020100"
            && hex (integer 127) == "02017f"
            && hex (integer 128) == "02020080"
            && hex (integer 255) == "020200ff"
            && hex (integer 256) == "02020100"),
        ("a length takes the fewest octets that hold it",
          hex (lengthBytes 0) == "00"
            && hex (lengthBytes 127) == "7f"
            && hex (lengthBytes 128) == "8180"
            && hex (lengthBytes 255) == "81ff"
            && hex (lengthBytes 256) == "820100"
            && hex (lengthBytes 65535) == "82ffff"
            && hex (lengthBytes 65536) == "83010000"),
        ("the primitives that carry no value are written as X.690 spells them",
          hex null == "0500"
            && hex (sequence ⟨#[]⟩) == "3000"
            && hex (bitString ⟨#[0xab, 0xcd]⟩) == "030300abcd"
            && hex (objectIdentifier rsaEncryptionOid) == "06092a864886f70d010101"),
        -- Generated with `openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048` and read
        -- out with `openssl pkey -pubout -outform DER`.
        ("an RSA SubjectPublicKeyInfo is the one OpenSSL writes for the same key",
          hex (rsaPublicKeyInfo rsaKey) == rsaSpki),
        ("that structure reads back as the key it was written from",
          publicKeyOfSpki (rsaPublicKeyInfo rsaKey) == some rsaKey),
        -- Generated with `openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256`.
        -- Nothing here reads it back: the reader knows only RSA.
        ("a P-256 SubjectPublicKeyInfo is the one OpenSSL writes for the same key",
          hex (ecPublicKeyInfo prime256v1Oid (bytesOfHex ecPoint)) == ecSpki),
        ("the reader refuses a key the writer will not produce a modulus for",
          publicKeyOfSpki (rsaPublicKeyInfo { modulus := 0, exponent := 65537 }) == none) ]

end Tests.DerWriter
