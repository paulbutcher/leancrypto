/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Lowercase hexadecimal.

Encoding is lowercase and always two characters per byte. Both matter to a consumer that puts a
digest into a signature: a request signed with uppercase hex, or with a leading zero dropped, is
rejected with a mismatch that says nothing about which of the two it was.
-/

@[expose] public section

namespace Codec.Hex

def digits : List Char := "0123456789abcdef".toList

def encodeNibble (n : Nat) : Char := digits.getD n '?'

/-- Accepts either case, since what is being read was not necessarily written here. -/
def decodeChar (c : Char) : Option Nat := digits.findIdx? (· == c.toLower)

def encode : List UInt8 → List Char
  | [] => []
  | b :: rest =>
    encodeNibble (b.toNat / 16) :: encodeNibble (b.toNat % 16) :: encode rest

def decode : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | x :: y :: rest =>
    match decodeChar x, decodeChar y, decode rest with
    | some high, some low, some tail => some (UInt8.ofNat (high * 16 + low) :: tail)
    | _, _, _ => none

def encodeString (bytes : ByteArray) : String := String.ofList (encode bytes.data.toList)

def decodeString (s : String) : Option ByteArray :=
  (decode s.toList).map fun bytes => ⟨bytes.toArray⟩

end Codec.Hex
