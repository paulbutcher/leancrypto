/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Crypto.Rsa

/-!
What the verification arithmetic rests on, proved rather than sampled: that square and multiply
computes the power it stands in for, and that a number is rendered to exactly the width the
comparison expects, with the value the comparison assumes.

The vectors in `Tests.RsaVectors` establish agreement with the standard. These establish that the
two functions the standard is implemented in terms of are the functions they are named after, for
every input rather than for the ones a published suite happens to contain.
-/

namespace Tests.Rsa
open Crypto.Rsa

theorem powMod_eq (base exponent modulus : Nat) :
    powMod base exponent modulus = base ^ exponent % modulus := by
  induction base, exponent using powMod.induct (modulus := modulus) with
  | case1 base => rw [powMod.eq_def]; simp
  | case2 base exponent hne heven ih =>
    rw [powMod.eq_def, if_neg hne, if_pos heven, ih, ← Nat.pow_mod, ← Nat.pow_two,
      ← Nat.pow_mul, show 2 * (exponent / 2) = exponent by omega]
  | case3 base exponent hne hodd ih =>
    rw [powMod.eq_def, if_neg hne, if_neg hodd, ih, ← Nat.pow_mod, ← Nat.pow_two,
      ← Nat.pow_mul, Nat.mod_mul_mod, ← Nat.pow_succ, Nat.succ_eq_add_one,
      show 2 * (exponent / 2) + 1 = exponent by omega]

private theorem digits_length : ∀ (length n : Nat) (tail : List UInt8),
    (digitsOfNat length n tail).length = length + tail.length
  | 0, _, _ => by simp [digitsOfNat]
  | length + 1, n, tail => by
    simp [digitsOfNat, digits_length length (n / 256)]
    omega

/-- The comparison in `verifyPkcs1v15Sha256` is against a block of exactly the modulus length, so
a rendering that dropped a leading zero would fail every signature rather than accept a wrong one.
It is still worth knowing which. -/
theorem bytesOfNat_size (length n : Nat) : (bytesOfNat length n).size = length := by
  simp [bytesOfNat, ByteArray.size, digits_length]

private def natOfList (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

private theorem digits_split : ∀ (length n : Nat) (tail : List UInt8),
    digitsOfNat length n tail = digitsOfNat length n [] ++ tail
  | 0, _, _ => by simp [digitsOfNat]
  | length + 1, n, tail => by
    rw [digitsOfNat, digits_split length (n / 256), digitsOfNat,
      digits_split length (n / 256) [UInt8.ofNat (n % 256)]]
    simp

private theorem natOfList_digits : ∀ (length n : Nat),
    natOfList (digitsOfNat length n []) = n % 256 ^ length
  | 0, n => by simp [digitsOfNat, natOfList, Nat.mod_one]
  | length + 1, n => by
    have ih := natOfList_digits length (n / 256)
    have hbyte : (UInt8.ofNat (n % 256)).toNat = n % 256 := by simp
    rw [natOfList] at ih
    rw [digitsOfNat, digits_split, natOfList, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, hbyte]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ length) 256, Nat.mod_mul]
    omega

/-- Rendering and reading back are inverse below the width, and above it the top is what is lost.
Together with `bytesOfNat_size` this is what makes the encode-and-compare check a comparison of
the number the standard names rather than of some other number with the same low bytes. -/
theorem natOfBytes_bytesOfNat (length n : Nat) :
    natOfBytes (bytesOfNat length n) = n % 256 ^ length := by
  rw [natOfBytes, bytesOfNat]
  simpa [natOfList] using natOfList_digits length n

end Tests.Rsa
