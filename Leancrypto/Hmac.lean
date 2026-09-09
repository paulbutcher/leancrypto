/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Leancrypto.Sha2

/-!
HMAC over SHA-256, SHA-384 or SHA-512 (RFC 2104).

The one thing here whose key is secret. It belongs in a pure Lean library anyway because SHA-2's
control flow does not depend on the bytes it is given: the same rounds run over the same block
count whatever the key is. What a caller must not assume is that comparing the result is equally
indifferent, which is what the note on `bytesEqual` records.
-/

public section

namespace Leancrypto

private def blockKey (digest : Sha2) (key : ByteArray) : ByteArray :=
  let shortened := if key.size > digest.blockSize then digest.hash key else key
  shortened ++ ⟨Array.replicate (digest.blockSize - shortened.size) 0⟩

/-- Takes and returns raw bytes rather than an encoding, because a key derivation chain feeds one
result into the next as a key. -/
def hmac (digest : Sha2) (key message : ByteArray) : ByteArray :=
  let padded := blockKey digest key
  let inner : ByteArray := ⟨padded.data.map (· ^^^ 0x36)⟩
  let outer : ByteArray := ⟨padded.data.map (· ^^^ 0x5c)⟩
  digest.hash (outer ++ digest.hash (inner ++ message))

def hmacUtf8 (digest : Sha2) (key message : String) : ByteArray :=
  hmac digest key.toUTF8 message.toUTF8

end Leancrypto
