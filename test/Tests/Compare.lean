/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Compare

/-!
Absence of an early exit is not a property a theorem here can state, so what is proved is the
other half: that the comparison written to avoid one still decides equality. A comparison that
leaked nothing and also accepted the wrong bytes would pass the eye and fail the point.
-/

namespace Tests.Compare
open Leancrypto

/--
Folding `Bool.and` over a list of booleans is the conjunction of the accumulator with every element.
`bytesEqual` combines its per-byte comparisons with a fold rather than with an early exit,
deliberately, and this converts that fold into the `all` form the rest of the reasoning can work
with.

`l.foldl Bool.and acc` walks `l` from the left, combining each element into `acc`, and `l.all id` is
`true` exactly when every element of `l` is `true`; the equation says the fold is that conjunction,
with the starting accumulator kept as a factor. Quantifying over `acc` as well as `l` is what lets
the induction step apply the hypothesis at an accumulator it has already changed, and it covers the
`true` that `bytesEqual` starts from. At `l = []` both sides are `acc`, so the base case is an
instance rather than an exception.
-/
private theorem foldl_and : ∀ (l : List Bool) (acc : Bool), l.foldl Bool.and acc = (acc && l.all id)
  | [], acc => by simp
  | x :: xs, acc => by simp [foldl_and xs, Bool.and_assoc]

/--
The body of `bytesEqual`, read at the level of lists, decides equality exactly: `true` on equal
lists and `false` on every other pair. Both directions are needed. A comparison that leaked no
timing and also accepted the wrong bytes would look right and be worth nothing, and one that
rejected bytes it should accept would fail every signature.

The left conjunct compares lengths and the right zips the two lists with `==` and folds `Bool.and`
over the results from `true`; the `↔` says that conjunction is `true` in precisely the cases where
`a` and `b` are the same list. The length test is not redundant: `zipWith` stops at the shorter
list, so without it a prefix would compare equal to what it is a prefix of. It is stated over
`List UInt8`, where `==` is decidable equality, so `x == y` being `true` really is `x = y`.
-/
private theorem list_iff : ∀ a b : List UInt8,
    ((a.length == b.length) && (List.zipWith (fun x y => x == y) a b).foldl Bool.and true) = true
      ↔ a = b
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    have ih := list_iff xs ys
    simp only [foldl_and, Bool.true_and] at ih ⊢
    simp only [List.length_cons, List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, Nat.add_right_cancel_iff, List.cons.injEq, id_eq] at ih ⊢
    constructor
    · rintro ⟨hlen, hx, hrest⟩
      exact ⟨hx, ih.mp ⟨hlen, hrest⟩⟩
    · rintro ⟨hx, hrest⟩
      obtain ⟨hlen, hall⟩ := ih.mpr hrest
      exact ⟨hlen, hx, hall⟩

/--
`bytesEqual` decides equality of byte arrays: `true` on equal arrays, `false` on every other pair.
This is the half of its contract a theorem can state. The absence of a data-dependent early exit is
a claim about the code Lean generates, not about any proposition here, and the module heading says
so.

`a` and `b` are arbitrary `ByteArray`s, destructured as `⟨da⟩` and `⟨db⟩` because a `ByteArray`
wraps an `Array UInt8`. `bytesEqual a b = true` is the function answering yes and `a = b` is
equality of the arrays, so the `↔` rules out a false accept in one direction and a false reject in
the other. Arrays of different sizes are covered rather than excluded: `bytesEqual` tests the sizes
first, and `list_iff` carries that test through to the underlying lists.
-/
theorem bytesEqual_iff : ∀ a b : ByteArray, bytesEqual a b = true ↔ a = b
  | ⟨da⟩, ⟨db⟩ => by
    simp only [bytesEqual, ByteArray.size, ByteArray.mk.injEq, ← Array.length_toList,
      list_iff, Array.toList_inj]

end Tests.Compare
