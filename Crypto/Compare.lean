/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Crypto

/--
Compares every byte. `==` stops at the first difference, which reports how long a correct prefix
a guess had; that is a usable oracle against a secret compared byte by byte, and it is why a MAC
must not be checked with ordinary equality.

This is not constant time and is deliberately not named as though it were. What it offers is the
absence of a data-dependent early exit in this source. Lean guarantees nothing about the code it
generates, the runtime is free to short-circuit the `Bool` operations, and nothing here addresses
cache or branch-predictor timing. A caller whose threat model needs a real guarantee needs a
native implementation and should not take this one for it.
-/
def bytesEqual (a b : ByteArray) : Bool :=
  a.size == b.size &&
    (List.zipWith (fun x y => x == y) a.data.toList b.data.toList).foldl Bool.and true

end Crypto
