/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Leancrypto.Codec.Hex
public import Leancrypto.Rsa

/-!
Reading the hexadecimal a NIST CAVP response file records its fields in.
-/

namespace Tests.Cavp
public section
open Leancrypto

/-- A field that is not hexadecimal becomes the empty byte string rather than a failure, which
turns a mistyped vector into a check that fails rather than one that cannot be written. -/
def bytesOfHex (hex : String) : ByteArray := (Codec.Hex.decodeString hex).getD ⟨#[]⟩

def natOfHex (hex : String) : Nat := Rsa.natOfBytes (bytesOfHex hex)

def digestName : Sha2 → String
  | .sha256 => "SHA-256"
  | .sha384 => "SHA-384"
  | .sha512 => "SHA-512"

def resultName (expected : Bool) : String := if expected then "P" else "F"

end
end Tests.Cavp
