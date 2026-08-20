/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Crypto.Compare

/-!
Absence of an early exit is not a property a theorem here can state, so what is proved is the
other half: that the comparison written to avoid one still decides equality. A comparison that
leaked nothing and also accepted the wrong bytes would pass the eye and fail the point.
-/

namespace Tests.Compare
open Crypto

private theorem foldl_and : ∀ (l : List Bool) (acc : Bool), l.foldl Bool.and acc = (acc && l.all id)
  | [], acc => by simp
  | x :: xs, acc => by simp [foldl_and xs, Bool.and_assoc]

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

theorem bytesEqual_iff : ∀ a b : ByteArray, bytesEqual a b = true ↔ a = b
  | ⟨da⟩, ⟨db⟩ => by
    simp only [bytesEqual, ByteArray.size, ByteArray.mk.injEq, ← Array.length_toList,
      list_iff, Array.toList_inj]

end Tests.Compare
