/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Leancrypto.Compare
public import Leancrypto.Sha2

/-!
RSASSA-PKCS1-v1_5 signature verification over SHA-256, SHA-384 or SHA-512 (RFC 8017 §8.2.2).

Everything here takes public inputs only: a public key, a message somebody sent, and a signature
somebody made. There is no secret, so there is nothing for a timing signal to leak, and nothing
here is written as though there were. That is also the boundary of what belongs under this
heading. Signing, and every other operation involving a private key, needs blinding, needs its
arithmetic to be independent of the key, and needs an implementation whose execution is
constrained in ways Lean does not constrain it; none of that is here, and none of it should be
added beneath the same heading on the strength of the name.

Verification is by encode and compare, never by decode and inspect. The expected block is built
from the message and compared whole against the recovered one. The alternative, walking the
recovered block, stepping over whatever padding is found and reading a digest off the end, is the
Bleichenbacher forgery of 2006: with a low exponent an attacker can construct a block that a
lenient parser accepts without the private key. It has been reimplemented independently many
times since. Encoding the expectation leaves no parser to be lenient.

RSA-PSS is `Leancrypto.Rsa.Pss`, in a module of its own because its discipline is not this one.
-/

@[expose] public section

namespace Leancrypto.Rsa

/-- No invariant a caller can break, because there is none to hold: both fields are public and
any pair of naturals is a well-formed thing to attempt a verification with. -/
structure PublicKey where
  modulus : Nat
  exponent : Nat
  deriving Repr, DecidableEq

/-- Square and multiply over the binary expansion of the exponent, reducing at every step.

Evaluating `base ^ exponent` and reducing afterwards is not an option: with a 2048-bit modulus
and the conventional exponent 65537 the intermediate result is some 130 million bits, and a
caller would see a hang rather than a failure. -/
def powMod (base exponent modulus : Nat) : Nat :=
  if exponent = 0 then 1 % modulus
  else
    let squared := powMod (base * base % modulus) (exponent / 2) modulus
    if exponent % 2 = 0 then squared else squared * base % modulus
decreasing_by omega

def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else bitLength (n / 2) + 1
decreasing_by omega

def byteLength (n : Nat) : Nat := (bitLength n + 7) / 8

def natOfBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- The big-endian digits of `n` in `length` bytes, in front of `tail`. -/
def digitsOfNat : Nat → Nat → List UInt8 → List UInt8
  | 0, _, tail => tail
  | length + 1, n, tail => digitsOfNat length (n / 256) (UInt8.ofNat (n % 256) :: tail)

/-- Big-endian, to exactly `length` bytes: shorter values keep their leading zeros, which the
comparison against the expected block depends on, and a value too large for the length is
truncated at the top rather than overflowing it. -/
def bytesOfNat (length n : Nat) : ByteArray := ⟨(digitsOfNat length n []).toArray⟩

/-- The `DigestInfo` prefix the digest of a message is written behind: `SEQUENCE { SEQUENCE { OID,
NULL }, OCTET STRING }`, with the bytes of the digest following.

RFC 8017 §9.2 gives one correct byte string per algorithm, so they are written out as three.
Assembling them with a general DER encoder would introduce a second thing capable of producing a
different answer, and the identifiers differ only in their last OID byte and two lengths. -/
def digestInfo : Sha2 → ByteArray
  | .sha256 =>
    ⟨#[0x30, 0x31,
       0x30, 0x0d,
       0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
       0x05, 0x00,
       0x04, 0x20]⟩
  | .sha384 =>
    ⟨#[0x30, 0x41,
       0x30, 0x0d,
       0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02,
       0x05, 0x00,
       0x04, 0x30]⟩
  | .sha512 =>
    ⟨#[0x30, 0x51,
       0x30, 0x0d,
       0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03,
       0x05, 0x00,
       0x04, 0x40]⟩

/-- Below this, refuse. A caller that genuinely has to verify a signature under a shorter modulus
needs an entry point that says so in its name, so that no caller reaches the weak behaviour by
default. -/
def minModulusBits : Nat := 2048

/-- `EM = 0x00 || 0x01 || 0xFF…0xFF || 0x00 || DigestInfo || H`, the block RFC 8017 §9.2 says a
signature over this message must recover. `none` when the modulus leaves no room for the eight
bytes of padding the standard requires. -/
def encodedMessage (digest : Sha2) (length : Nat) (message : ByteArray) : Option ByteArray :=
  let hashed := digest.hash message
  let info := digestInfo digest
  let infoLength := info.size + hashed.size
  if length < infoLength + 11 then none
  else
    let padding : ByteArray := ⟨Array.replicate (length - infoLength - 3) 0xff⟩
    some (⟨#[0x00, 0x01]⟩ ++ padding ++ ⟨#[0x00]⟩ ++ info ++ hashed)

/-- The message itself rather than its digest: nothing in the types would connect a digest handed
in by a caller to the algorithm named in the `DigestInfo` this builds, so a caller hashing with
the wrong function would get a `true`. -/
def verifyPkcs1v15 (digest : Sha2) (key : PublicKey) (message signature : ByteArray) : Bool :=
  let length := byteLength key.modulus
  if bitLength key.modulus < minModulusBits then false
  else if signature.size != length then false
  else
    let representative := natOfBytes signature
    -- RSAVP1 refuses a representative outside the range of the modulus. Reducing it instead
    -- would make every signature one of many that verify.
    if representative ≥ key.modulus then false
    else
      match encodedMessage digest length message with
      | none => false
      | some expected =>
        -- `bytesEqual` rather than `==` for consistency with the rest of the library. Nothing here
        -- needs it: both blocks are derived from public inputs.
        bytesEqual (bytesOfNat length (powMod representative key.exponent key.modulus)) expected

end Leancrypto.Rsa
