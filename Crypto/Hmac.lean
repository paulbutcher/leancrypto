/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Crypto.Sha256

/-!
HMAC-SHA256 (RFC 2104).
-/

public section

namespace Crypto

private def blockSize : Nat := 64

private def blockKey (key : ByteArray) : ByteArray :=
  let shortened := if key.size > blockSize then Sha256.hash key else key
  shortened ++ ⟨Array.replicate (blockSize - shortened.size) 0⟩

/-- Takes and returns raw bytes rather than an encoding, because a key derivation chain feeds one
result into the next as a key. -/
def hmac (key message : ByteArray) : ByteArray :=
  let padded := blockKey key
  let inner : ByteArray := ⟨padded.data.map (· ^^^ 0x36)⟩
  let outer : ByteArray := ⟨padded.data.map (· ^^^ 0x5c)⟩
  Sha256.hash (outer ++ Sha256.hash (inner ++ message))

def hmacUtf8 (key message : String) : ByteArray := hmac key.toUTF8 message.toUTF8

end Crypto
