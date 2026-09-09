/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Leancrypto.Der.Reader

/-!
Writing the same subset of DER that `Leancrypto.Der.Reader` reads.

The reader refuses every spelling but one, so the writer has only one to produce: a length in the
fewest octets that hold it, an integer in the fewest that keep it positive, and no indefinite
lengths anywhere. That is why the two belong together. A writer whose output its own reader
refuses, or accepts as something else, is a bug that only having both in one place makes visible.

Nothing here is secret and nothing here is parsing. A caller hands in values it already has and
gets the octets that name them.
-/

@[expose] public section

namespace Leancrypto.Der

/-- The base-256 digits of `n`, big-endian, with no leading zero, and a single zero digit for
`n = 0`. This is the shortest form, which is the only one DER admits. -/
def base256 (n : Nat) : List UInt8 :=
  if n < 256 then [UInt8.ofNat n] else base256 (n / 256) ++ [UInt8.ofNat (n % 256)]
decreasing_by omega

/-- The length octets: the short form below 128, and otherwise a count of following octets and the
length in that many. The reader refuses a long form with more octets than it needs and refuses more
than eight of them; eight octets address more than any `ByteArray` this could be handed, so the
second is not a limit a caller can reach. -/
def lengthBytes (n : Nat) : ByteArray :=
  if n < 0x80 then ⟨#[UInt8.ofNat n]⟩
  else
    let digits := base256 n
    ⟨(UInt8.ofNat (0x80 + digits.length) :: digits).toArray⟩

def tlv (tag : UInt8) (contents : ByteArray) : ByteArray :=
  ⟨#[tag]⟩ ++ lengthBytes contents.size ++ contents

def sequence (contents : ByteArray) : ByteArray := tlv sequenceTag contents

/-- A non-negative `INTEGER`. DER reads the top bit of the first octet as a sign, so a value whose
own first octet has that bit set is written behind a zero octet, and one whose first octet does not
is written without one. Adding the octet unconditionally, or never, would each produce something
the reader refuses. -/
def integer (n : Nat) : ByteArray :=
  let digits := base256 n
  tlv integerTag ⟨(if digits.head?.getD 0 ≥ 0x80 then 0x00 :: digits else digits).toArray⟩

/-- A `BIT STRING` of whole octets, so the count of unused trailing bits is zero. The reader
refuses any other count, because a key is a whole number of octets. -/
def bitString (contents : ByteArray) : ByteArray := tlv bitStringTag (⟨#[0x00]⟩ ++ contents)

/-- Takes the identifier's contents rather than its dotted form, matching `readObjectIdentifier`,
which compares against contents. Encoding the dotted form would be a second thing capable of
producing a different answer from the constants both sides are written with. -/
def objectIdentifier (oid : ByteArray) : ByteArray := tlv objectIdentifierTag oid

def null : ByteArray := tlv nullTag ⟨#[]⟩

end Leancrypto.Der
