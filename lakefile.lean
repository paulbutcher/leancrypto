/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open System Lake DSL

package leancrypto where
  version := v!"0.4.2"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

/-- One library, and every module under `Leancrypto`. Lake builds the modules a consumer imports
rather than the libraries it requires, so splitting this into an encoding target and a
cryptography target would not spare anyone a module they do not import. -/
@[default_target]
lean_lib Leancrypto

@[test_driver]
script tests (args) do
  let pkg ← getRootPackage
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["test", "--"] ++ args.toArray
    cwd := pkg.dir / "test"
  }
  child.wait
