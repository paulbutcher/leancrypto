/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Tests

/-!
Most of the suite is theorems, which pass by compiling. What remains here are the published
vectors, whose value is agreement with a constant no proof could establish.
-/

public def main : IO UInt32 := do
  let checks := Tests.Vectors.checks ++ Tests.RsaVectors.checks ++ Tests.Der.checks
  let failed := checks.filter fun (_, passed) => !passed
  for (name, _) in failed do
    IO.eprintln s!"FAILED: {name}"
  if failed.isEmpty then
    IO.println s!"{checks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failed.length} of {checks.length} checks failed"
    return 1
