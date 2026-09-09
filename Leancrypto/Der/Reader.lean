/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
As much of DER (X.690) as reading a public key out of a certificate needs: `SEQUENCE`, `INTEGER`,
`BIT STRING`, `OBJECT IDENTIFIER` and `NULL`, read from a byte array by index.

Every input here is attacker-supplied by construction, because a verifier is reachable from an
unauthenticated endpoint. So nothing indexes without a bound, nothing recurses without a
structural argument, and every reader refuses what it does not understand rather than skipping
it. In particular it refuses indefinite lengths, lengths that reach past the end of their
container, lengths spelled with more bytes than they need, and integers that are negative or
carry a leading zero they do not need. Each of those is a place where a permissive ASN.1 parser
becomes a way to make one certificate read as two different things.

Reading is bounded by an explicit `limit` rather than by the size of the array, so that a nested
structure cannot read its way out of its parent and into whatever follows.
-/

@[expose] public section

namespace Leancrypto.Der

def sequenceTag : UInt8 := 0x30
def integerTag : UInt8 := 0x02
def bitStringTag : UInt8 := 0x03
def nullTag : UInt8 := 0x05
def objectIdentifierTag : UInt8 := 0x06

/-- The `[0]` of an X.509 `tbsCertificate`, which is the only context-specific tag this reads. -/
def contextZeroTag : UInt8 := 0xA0

/-- A tag and the extent of its contents. `next` is where the value after this one begins. -/
structure Tlv where
  tag : UInt8
  start : Nat
  length : Nat
  deriving Repr, DecidableEq

def Tlv.next (tlv : Tlv) : Nat := tlv.start + tlv.length

def byteAt (der : ByteArray) (limit index : Nat) : Option UInt8 :=
  if index < limit then der.data[index]? else none

def readBase256 (der : ByteArray) (limit : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, acc => some acc
  | count + 1, index, acc =>
    match byteAt der limit index with
    | none => none
    | some byte => readBase256 der limit count (index + 1) (acc * 256 + byte.toNat)

/-- The length octets, and where the value begins. `0x80` is the indefinite form, which BER allows
and DER does not; the long form is refused when it is longer than it needs to be, so that one
length has one spelling. -/
def readLength (der : ByteArray) (limit index : Nat) : Option (Nat × Nat) := do
  let first ← byteAt der limit index
  if first < 0x80 then
    some (first.toNat, index + 1)
  else if first = 0x80 then
    none
  else
    let count := (first - 0x80).toNat
    -- Eight octets address more than any input this will be handed, and refusing more keeps the
    -- arithmetic below in a range that cannot be made to grow.
    guard (count ≤ 8)
    let leading ← byteAt der limit (index + 1)
    guard (leading ≠ 0)
    let length ← readBase256 der limit count (index + 1) 0
    guard (length ≥ 0x80)
    some (length, index + 1 + count)

def readTlv (der : ByteArray) (limit index : Nat) : Option Tlv := do
  let tag ← byteAt der limit index
  let (length, start) ← readLength der limit (index + 1)
  guard (start + length ≤ limit)
  some { tag, start, length }

def readTagged (tag : UInt8) (der : ByteArray) (limit index : Nat) : Option Tlv := do
  let tlv ← readTlv der limit index
  guard (tlv.tag = tag)
  some tlv

/-- Where the value at `index` ends, without interpreting it. This is how the fields of a
certificate that are not the key are passed over; it still parses each one's length, so a field
that overruns its container is refused rather than skipped. -/
def skipValue (der : ByteArray) (limit index : Nat) : Option Nat :=
  (readTlv der limit index).map Tlv.next

/-- A non-negative `INTEGER`, and where it ends. DER spells an integer in the fewest bytes that
keep it positive, so a leading zero is accepted only in front of a byte that would otherwise read
as a sign bit, and rejected everywhere else. -/
def readNat (der : ByteArray) (limit index : Nat) : Option (Nat × Nat) := do
  let tlv ← readTagged integerTag der limit index
  guard (tlv.length ≥ 1)
  let first ← byteAt der limit tlv.start
  guard (first < 0x80)
  if first = 0 then
    if tlv.length = 1 then
      some (0, tlv.next)
    else do
      let second ← byteAt der limit (tlv.start + 1)
      guard (second ≥ 0x80)
      let value ← readBase256 der limit tlv.length tlv.start 0
      some (value, tlv.next)
  else do
    let value ← readBase256 der limit tlv.length tlv.start 0
    some (value, tlv.next)

/-- The bytes a `BIT STRING` carries, as a range. A key is a whole number of bytes, so a count of
unused bits other than zero is a different thing from the thing being read, and is refused. -/
def readBitString (der : ByteArray) (limit index : Nat) : Option (Nat × Nat) := do
  let tlv ← readTagged bitStringTag der limit index
  guard (tlv.length ≥ 1)
  let unused ← byteAt der limit tlv.start
  guard (unused = 0)
  some (tlv.start + 1, tlv.next)

/-- An `OBJECT IDENTIFIER` with exactly the expected contents, and where it ends. The caller says
which identifier it will accept, because an algorithm identifier that is merely well-formed is
how a caller ends up verifying an RSA signature against a key that was never an RSA key. -/
def readObjectIdentifier (expected : ByteArray) (der : ByteArray) (limit index : Nat) :
    Option Nat := do
  let tlv ← readTagged objectIdentifierTag der limit index
  guard (tlv.length = expected.size)
  guard ((der.extract tlv.start tlv.next).data = expected.data)
  some tlv.next

def readNull (der : ByteArray) (limit index : Nat) : Option Nat := do
  let tlv ← readTagged nullTag der limit index
  guard (tlv.length = 0)
  some tlv.next

end Leancrypto.Der
