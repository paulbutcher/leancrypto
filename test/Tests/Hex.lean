/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Codec.Hex

/-!
What a consumer putting a digest into a signature depends on: the encoding round-trips, it emits
two characters per byte so a leading zero cannot vanish, and it emits lowercase.
-/

namespace Tests.HexCodec
open Codec.Hex

private theorem nibble_roundTrip : ∀ n ∈ List.range 16, decodeChar (encodeNibble n) = some n := by
  decide

private theorem nr {n : Nat} (h : n < 16) : decodeChar (encodeNibble n) = some n :=
  nibble_roundTrip n (List.mem_range.mpr h)

private theorem nibble_mem : ∀ n ∈ List.range 16, encodeNibble n ∈ digits := by decide

private theorem nm {n : Nat} (h : n < 16) : encodeNibble n ∈ digits :=
  nibble_mem n (List.mem_range.mpr h)

private theorem digits_lower : ∀ c ∈ digits, c.toLower = c := by decide

private theorem decode_cons (x y : Char) (rest : List Char) :
    decode (x :: y :: rest) =
    match decodeChar x, decodeChar y, decode rest with
    | some high, some low, some tail => some (UInt8.ofNat (high * 16 + low) :: tail)
    | _, _, _ => none := rfl

theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    have hb : b.toNat < 256 := b.toNat_lt_size
    simp only [encode, decode_cons, nr (show b.toNat / 16 < 16 by omega),
      nr (show b.toNat % 16 < 16 by omega), ih,
      show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat by omega, UInt8.ofNat_toNat]

/-- Two characters per byte, so a byte below sixteen keeps its leading zero. -/
theorem length_encode (bytes : List UInt8) : (encode bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    simp only [encode, List.length_cons, ih]
    omega

theorem encode_lower (bytes : List UInt8) : ∀ c ∈ encode bytes, c.toLower = c := by
  induction bytes with
  | nil => intro c hc; simp only [encode, List.not_mem_nil] at hc
  | cons b rest ih =>
    intro c hc
    have hb : b.toNat < 256 := b.toNat_lt_size
    simp only [encode, List.mem_cons] at hc
    rcases hc with h | h | h
    · subst h; exact digits_lower _ (nm (by omega))
    · subst h; exact digits_lower _ (nm (by omega))
    · exact ih c h

end Tests.HexCodec
