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

/--
Square and multiply computes the power it stands in for. Verification cannot evaluate
`base ^ exponent` and reduce afterwards, since with a 2048-bit modulus the intermediate result runs
to some 130 million bits, so the function it does use has to be shown to be the function it is named
after. Agreement sampled on published vectors would leave every exponent nobody published untested.

`powMod base exponent modulus` is the halve-and-square recursion and `base ^ exponent % modulus` is
the value RFC 8017 names, so the equation is agreement for every triple of naturals with no side
condition attached. Nothing is excluded in order to make it true: a `modulus` of `0` or `1` is
included, and `%` gives both sides the same answer there. The induction is over `powMod.induct`, so
its cases are the function's own recursion rather than a scheme chosen to suit the statement.
-/
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

/--
`digitsOfNat` contributes exactly `length` digits, however large the number it is rendering. That is
what makes the width of a rendered block a property of the requested length alone, which is the form
the comparison in `verifyPkcs1v15Sha256` needs.

`digitsOfNat length n tail` puts the big-endian digits of `n` in front of `tail`, and the equation
says the result is `length` longer than `tail` was. The count does not mention `n`, which is why a
value too large for the width is truncated at the top rather than overflowing it, and why a small
value keeps leading zeros rather than shrinking. Generalising over `tail` is what lets the induction
step apply the hypothesis at the list it has already accumulated.
-/
private theorem digits_length : ∀ (length n : Nat) (tail : List UInt8),
    (digitsOfNat length n tail).length = length + tail.length
  | 0, _, _ => by simp [digitsOfNat]
  | length + 1, n, tail => by
    simp [digitsOfNat, digits_length length (n / 256)]
    omega

/--
A number rendered to `length` bytes occupies exactly `length` bytes, whatever its magnitude. The
comparison in `verifyPkcs1v15Sha256` is against a block of exactly the modulus length, so a
rendering that dropped a leading zero would fail every signature rather than accept a wrong one;
which of those two a width bug causes is worth knowing rather than guessing.

`bytesOfNat length n` is the big-endian rendering as a `ByteArray` and `.size` is its byte count,
fixed here at the requested `length` for every `n`. Both extremes are inside the claim rather than
excluded from it: `n = 0` renders as `length` zero bytes, and an `n` too large renders as its low
`length` bytes. It says nothing about what those bytes are worth; that is `natOfBytes_bytesOfNat`.
-/
theorem bytesOfNat_size (length n : Nat) : (bytesOfNat length n).size = length := by
  simp [bytesOfNat, ByteArray.size, digits_length]

private def natOfList (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/--
The accumulator `digitsOfNat` threads through its recursion is only ever appended to, never read or
altered. Without that, the digits of a number could not be reasoned about apart from whatever list
they were being placed in front of.

The left builds the digits of `n` directly in front of `tail`; the right builds them in front of the
empty list and appends `tail` afterwards. Their equality, for every `length`, `n` and `tail`, says
the tail passes through untouched, which is what lets `natOfList_digits` be stated at `[]` and still
describe every call the renderer makes.
-/
private theorem digits_split : ∀ (length n : Nat) (tail : List UInt8),
    digitsOfNat length n tail = digitsOfNat length n [] ++ tail
  | 0, _, _ => by simp [digitsOfNat]
  | length + 1, n, tail => by
    rw [digitsOfNat, digits_split length (n / 256), digitsOfNat,
      digits_split length (n / 256) [UInt8.ofNat (n % 256)]]
    simp

/--
Reading the digits back gives the number that was rendered when it fits the width, and its low bytes
when it does not. This is where the round trip actually happens; what follows only carries the same
fact across the `ByteArray` wrapper.

`natOfList` folds the bytes big-endian as `acc * 256 + byte`, which is what `natOfBytes` does over
an array, and `digitsOfNat length n []` is the rendering with nothing after it. `n % 256 ^ length`
is `n` itself exactly when `n < 256 ^ length`, and the truncation from the top otherwise, so the one
equation states both the round trip and what is lost when there is no room. `length = 0` is not an
exception: both sides are `0`, since `n % 1` is `0`.
-/
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

/--
Rendering a number and reading it back are inverse below the width, and above it the top is what is
lost. Together with `bytesOfNat_size` this is what makes the encode-and-compare check in
`verifyPkcs1v15Sha256` a comparison of the number the standard names, rather than of some other
number that shares its low bytes.

`bytesOfNat length n` renders `n` big-endian into `length` bytes and `natOfBytes` reads a
`ByteArray` back big-endian, so the equation is a round trip whenever `n < 256 ^ length` and says
exactly what survives otherwise. That verification only ever renders values in the first case
follows from `length` being `byteLength` of the modulus and the value being already reduced below
that modulus; nothing in this library proves that connection between `byteLength` and the size of
its argument, and it is assumed here rather than established.
-/
theorem natOfBytes_bytesOfNat (length n : Nat) :
    natOfBytes (bytesOfNat length n) = n % 256 ^ length := by
  rw [natOfBytes, bytesOfNat]
  simpa [natOfList] using natOfList_digits length n

end Tests.Rsa
