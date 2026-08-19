/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Base64 (RFC 4648 §4) with `=` padding, over the standard `+/` alphabet.

This is a different codec from `Codec.Base64Url` rather than a setting on it. The two alphabets
disagree on two characters, and a decoder that accepted either would hide which one the producer
used; `-` and `_` are rejected here for that reason. PEM bodies, and the signature fields of the
payloads this exists for, are written in this alphabet.

Bits beyond the encoded bytes are required to be zero, and padding is required to be exactly as
long as the final group is short, so a byte string has exactly one accepted encoding.

Line breaks are dropped before decoding, because PEM wraps at 64 columns and a caller that had to
strip them itself would one day forget.
-/

namespace Codec.Base64

def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

def pad : Char := '='

def encodeSextet (n : Nat) : Char := alphabet.getD n pad

def decodeChar (c : Char) : Option Nat := alphabet.findIdx? (· == c)

def encode : List UInt8 → List Char
  | [] => []
  | [a] =>
    let n := a.toNat
    [encodeSextet (n / 4), encodeSextet (n % 4 * 16), pad, pad]
  | [a, b] =>
    let n := a.toNat * 256 + b.toNat
    [encodeSextet (n / 1024), encodeSextet (n / 16 % 64), encodeSextet (n % 16 * 4), pad]
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    encodeSextet (n / 262144) :: encodeSextet (n / 4096 % 64) :: encodeSextet (n / 64 % 64)
      :: encodeSextet (n % 64) :: encode rest

def oneByte (s0 s1 : Nat) : Option (List UInt8) :=
  if s1 % 16 == 0 then some [UInt8.ofNat (s0 * 4 + s1 / 16)] else none

def twoBytes (s0 s1 s2 : Nat) : Option (List UInt8) :=
  if s2 % 4 == 0 then
    some [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4)]
  else none

def threeBytes (s0 s1 s2 s3 : Nat) : List UInt8 :=
  [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4),
    UInt8.ofNat (s2 % 4 * 64 + s3)]

def fullGroup (x y z w : Char) : Option (List UInt8) :=
  match decodeChar x, decodeChar y, decodeChar z, decodeChar w with
  | some s0, some s1, some s2, some s3 => some (threeBytes s0 s1 s2 s3)
  | _, _, _, _ => none

/-- Only the last group may be padded, and `decodeChar pad` is `none`, so an earlier group
containing `=` is rejected by `fullGroup` without a separate check for misplaced padding. -/
def finalGroup (x y z w : Char) : Option (List UInt8) :=
  if w == pad then
    if z == pad then
      match decodeChar x, decodeChar y with
      | some s0, some s1 => oneByte s0 s1
      | _, _ => none
    else
      match decodeChar x, decodeChar y, decodeChar z with
      | some s0, some s1, some s2 => twoBytes s0 s1 s2
      | _, _, _ => none
  else fullGroup x y z w

def decode : List Char → Option (List UInt8)
  | [] => some []
  | [x, y, z, w] => finalGroup x y z w
  | x :: y :: z :: w :: rest =>
    match fullGroup x y z w, decode rest with
    | some bytes, some tail => some (bytes ++ tail)
    | _, _ => none
  | _ => none

def keep (c : Char) : Bool := c != '\n' && c != '\r'

def encodeString (bytes : ByteArray) : String := String.ofList (encode bytes.data.toList)

def decodeString (s : String) : Option ByteArray :=
  (decode (s.toList.filter keep)).map fun bytes => ⟨bytes.toArray⟩

end Codec.Base64
