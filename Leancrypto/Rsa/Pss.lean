/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Leancrypto.Rsa

/-!
RSASSA-PSS signature verification (RFC 8017 §8.1.2), over SHA-256, SHA-384 or SHA-512.

A module of its own because its discipline is the opposite of the one `Leancrypto.Rsa` states.
PSS cannot be verified by encoding the expectation and comparing: the salt is chosen at signing
time and is not derivable from the message, so the block has to be taken apart. That is safe here
in a way it is not for PKCS#1 v1.5, because no byte of the block is free. The mask is the digest
of a field of the block itself, so an attacker cannot choose the recovered bytes without
inverting the digest, and every octet before the salt is pinned to a value rather than merely
being skipped over. What makes the v1.5 forgery work is a parser that steps over bytes it has no
expectation for; there are none of those here.

The salt length is given by the caller and not read back out of the block. Recovering it, which
OpenSSL calls `auto`, accepts a signature made with any length; a protocol that pins the length,
as JOSE pins it to the digest length, must refuse the others.
-/

public section

namespace Leancrypto.Rsa.Pss

/-- A byte with its top `count` bits set, and no bits set at all when `count` is zero. Written as
arithmetic because a shift by a whole word is not a whole-word shift on `UInt8`. -/
private def topBits (count : Nat) : UInt8 := UInt8.ofNat (255 - 255 / 2 ^ count)

private def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨(List.zipWith (· ^^^ ·) a.data.toList b.data.toList).toArray⟩

/-- MGF1 (RFC 8017 appendix B.2.1): the digest of the seed followed by a four-byte counter,
concatenated until `length` bytes are available, then cut to length.

The last block is generated whole and discarded from, rather than the digest being asked for a
partial output, because a digest has no partial output. -/
def mgf1 (digest : Sha2) (seed : ByteArray) (length : Nat) : ByteArray := Id.run do
  let mut mask : ByteArray := ⟨#[]⟩
  for counter in [0:(length + digest.size - 1) / digest.size] do
    mask := mask ++ digest.hash (seed ++ bytesOfNat 4 counter)
  pure (mask.extract 0 length)

/-- EMSA-PSS-VERIFY (RFC 8017 §9.1.2) against an already recovered block.

`emBits` is one less than the modulus in bits, so the block is at most as wide as the modulus and
the bits it cannot reach are required to be zero. Every step that can refuse does refuse: the
`0xbc` trailer, the unused leading bits of the masked `DB`, the zero run in front of the salt, the
`0x01` that ends it, and finally the digest. A verifier that dropped any one of them would still
agree with every positive vector ever published. -/
def verifyEncoded (digest : Sha2) (saltLength emBits : Nat) (message em : ByteArray) : Bool :=
  let hashLength := digest.size
  let emLength := em.size
  if emLength < hashLength + saltLength + 2 then false
  else if em.data.getD (emLength - 1) 0 != 0xbc then false
  else
    let dbLength := emLength - hashLength - 1
    let maskedDb := em.extract 0 dbLength
    let h := em.extract dbLength (dbLength + hashLength)
    let unused := topBits (8 * emLength - emBits)
    if maskedDb.data.getD 0 0 &&& unused != 0 then false
    else
      let db := xorBytes maskedDb (mgf1 digest h dbLength)
      let cleared : ByteArray := ⟨db.data.modify 0 (· &&& ~~~unused)⟩
      let zeroLength := dbLength - saltLength - 1
      if (cleared.extract 0 zeroLength).data.any (· != 0) then false
      else if cleared.data.getD zeroLength 0 != 0x01 then false
      else
        let salt := cleared.extract (zeroLength + 1) dbLength
        let salted := ⟨Array.replicate 8 0⟩ ++ digest.hash message ++ salt
        bytesEqual (digest.hash salted) h

/-- The message itself rather than its digest, for the reason `Rsa.verifyPkcs1v15` gives: nothing
in the types would tie a digest handed in by a caller to the one this recomputes.

`minModulusBits` applies here too, and for the same reason. -/
def verify (digest : Sha2) (saltLength : Nat) (key : PublicKey) (message signature : ByteArray) :
    Bool :=
  let modulusBits := bitLength key.modulus
  if modulusBits < minModulusBits then false
  else if signature.size != byteLength key.modulus then false
  else
    let representative := natOfBytes signature
    if representative ≥ key.modulus then false
    else
      let emBits := modulusBits - 1
      let emLength := (emBits + 7) / 8
      let recovered := powMod representative key.exponent key.modulus
      -- A representative too wide for the block is what RFC 8017 §8.1.2 calls an integer too
      -- large. `bytesOfNat` would truncate it into a different, narrower block.
      if byteLength recovered > emLength then false
      else verifyEncoded digest saltLength emBits message (bytesOfNat emLength recovered)

end Leancrypto.Rsa.Pss
