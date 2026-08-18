/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Codec.Hex
import Crypto.Hmac

/-!
Published vectors for SHA-256 (FIPS 180-4) and HMAC-SHA256 (RFC 4231). These are examples rather
than theorems by the escalation in `CLAUDE.md`, and deliberately so: the claim being checked is
agreement with a published constant, which no proof about this code could establish.
-/

namespace Tests.Vectors
open Crypto

private def hex (bytes : ByteArray) : String := Codec.Hex.encodeString bytes

private def bytesOf (s : String) : ByteArray := s.toUTF8

private def repeated (byte : UInt8) (count : Nat) : ByteArray := ⟨Array.replicate count byte⟩

def checks : List (String × Bool) :=
  [ ("sha256 of the empty message",
      hex (Sha256.hash ⟨#[]⟩) ==
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("sha256 of \"abc\"",
      hex (Sha256.hashUtf8 "abc") ==
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    -- 56 bytes, which is where the length field no longer fits in the final block and a further
    -- block is required. An implementation that gets that wrong passes every shorter vector.
    ("sha256 of the 56-character vector",
      hex (Sha256.hashUtf8
          "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("sha256 of a message longer than one block",
      hex (Sha256.hashUtf8 (String.ofList (List.replicate 1000 'a'))) ==
        "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"),
    -- RFC 4231 case 1.
    ("hmac-sha256 with a 20-byte key",
      hex (hmac (repeated 0x0b 20) (bytesOf "Hi There")) ==
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
    -- RFC 4231 case 2, where the key is shorter than the block.
    ("hmac-sha256 with a short key",
      hex (hmac (bytesOf "Jefe") (bytesOf "what do ya want for nothing?")) ==
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
    -- RFC 4231 case 3.
    ("hmac-sha256 with a full-block key",
      hex (hmac (repeated 0xaa 20) (repeated 0xdd 50)) ==
        "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
    -- RFC 4231 case 6, where the key is longer than the block and is hashed first.
    ("hmac-sha256 with an oversized key",
      hex (hmac (repeated 0xaa 131)
          (bytesOf "Test Using Larger Than Block-Size Key - Hash Key First")) ==
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
    -- RFC 4231 case 7, an oversized key with a message spanning several blocks.
    ("hmac-sha256 with an oversized key and a long message",
      hex (hmac (repeated 0xaa 131)
          (bytesOf ("This is a test using a larger than block-size key and a larger than " ++
            "block-size data. The key needs to be hashed before being used by the HMAC " ++
            "algorithm."))) ==
        "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2") ]

end Tests.Vectors
