/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open System Lake DSL

package leancrypto where
  version := v!"0.3.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩]

/-- Separate targets, so that a consumer needing only an encoding does not build a hash function,
and so that the encodings are not described as cryptography. `Codec` and `Crypto` do not depend on
each other.

`Der` is neither: reading a certificate is parsing, not cryptography, and the same reader is what a
certificate inspector or a key loader would want. It depends on both, because the structure it
reads is armoured in base64 and the thing it returns is an RSA key. -/
@[default_target]
lean_lib Crypto

@[default_target]
lean_lib Codec

@[default_target]
lean_lib Der

@[test_driver]
script tests (args) do
  let pkg ← getRootPackage
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["test", "--"] ++ args.toArray
    cwd := pkg.dir / "test"
  }
  child.wait
