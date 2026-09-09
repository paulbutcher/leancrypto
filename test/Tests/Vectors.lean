/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Hex
import Leancrypto.Hmac
import Leancrypto.Sha2

/-!
Published vectors for SHA-256, SHA-384 and SHA-512 (FIPS 180-4) and for HMAC over each of them
(RFC 4231). These are examples rather
than theorems by the escalation in `CLAUDE.md`, and deliberately so: the claim being checked is
agreement with a published constant, which no proof about this code could establish.
-/

namespace Tests.Vectors
open Leancrypto

private def hex (bytes : ByteArray) : String := Leancrypto.Codec.Hex.encodeString bytes

private def bytesOf (s : String) : ByteArray := s.toUTF8

private def repeated (byte : UInt8) (count : Nat) : ByteArray := ⟨Array.replicate count byte⟩

private def letters (count : Nat) : String := String.ofList (List.replicate count (Char.ofNat 97))

/-- The 896-bit vector of FIPS 180-4 appendix D, whose 112 bytes leave no room for the 512
family's 17-byte tail and so force a second block. -/
private def oversizedKeyMessage : String :=
  "Test Using Larger Than Block-Size Key - Hash Key First"

private def longMessage : String :=
  "This is a test using a larger than block-size key and a larger than block-size data. " ++
  "The key needs to be hashed before being used by the HMAC algorithm."

private def vector896 : String :=
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
  "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

public def checks : List (String × Bool) :=
  [ ("sha256 of the empty message",
      hex (Sha256.hash ⟨#[]⟩) ==
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("sha256 of \"abc\"",
      hex (Sha256.hashUtf8 "abc") ==
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    -- 64 bytes, exactly one block, so the padding occupies a block of its own.
    ("sha256 of a message filling a block exactly",
      hex (Sha256.hashUtf8 (letters 64)) ==
        "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"),
    -- 56 bytes, which is where the length field no longer fits in the final block and a further
    -- block is required. An implementation that gets that wrong passes every shorter vector.
    ("sha256 of the 56-character vector",
      hex (Sha256.hashUtf8
          "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("sha256 of a message longer than one block",
      hex (Sha256.hashUtf8 (letters 1000)) ==
        "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"),
    ("sha384 of the empty message",
      hex (Sha384.hash ⟨#[]⟩) ==
        "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da" ++
        "274edebfe76f65fbd51ad2f14898b95b"),
    ("sha384 of \"abc\"",
      hex (Sha384.hashUtf8 "abc") ==
        "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed" ++
        "8086072ba1e7cc2358baeca134c825a7"),
    ("sha384 of the 112-character vector",
      hex (Sha384.hashUtf8 vector896) ==
        "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712" ++
        "fcc7c71a557e2db966c3e9fa91746039"),
    ("sha384 of a message filling a block exactly",
      hex (Sha384.hashUtf8 (letters 128)) ==
        "edb12730a366098b3b2beac75a3bef1b0969b15c48e2163c23d96994f8d1bef7" ++
        "60c7e27f3c464d3829f56c0d53808b0b"),
    ("sha384 of a message longer than one block",
      hex (Sha384.hashUtf8 (letters 1000)) ==
        "f54480689c6b0b11d0303285d9a81b21a93bca6ba5a1b4472765dca4da45ee32" ++
        "8082d469c650cd3b61b16d3266ab8ced"),
    ("sha512 of the empty message",
      hex (Sha512.hash ⟨#[]⟩) ==
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce" ++
        "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
    ("sha512 of \"abc\"",
      hex (Sha512.hashUtf8 "abc") ==
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
        "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
    ("sha512 of the 112-character vector",
      hex (Sha512.hashUtf8 vector896) ==
        "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
        "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"),
    ("sha512 of a message filling a block exactly",
      hex (Sha512.hashUtf8 (letters 128)) ==
        "b73d1929aa615934e61a871596b3f3b33359f42b8175602e89f7e06e5f658a24" ++
        "3667807ed300314b95cacdd579f3e33abdfbe351909519a846d465c59582f321"),
    ("sha512 of a message longer than one block",
      hex (Sha512.hashUtf8 (letters 1000)) ==
        "67ba5535a46e3f86dbfbed8cbbaf0125c76ed549ff8b0b9e03e0c88cf90fa634" ++
        "fa7b12b47d77b694de488ace8d9a65967dc96df599727d3292a8d9d447709c97"),
    -- RFC 4231 cases 1, 2, 3, 6 and 7, over each digest. Case 3's key is shorter than every
    -- block here and case 6's is longer than every block here, so both paths through `blockKey`
    -- are exercised at each of the two block sizes.
    ("hmac-sha256 with a 20-byte key",
      hex (hmac .sha256 (repeated 0x0b 20) (bytesOf "Hi There")) ==
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
    ("hmac-sha384 with a 20-byte key",
      hex (hmac .sha384 (repeated 0x0b 20) (bytesOf "Hi There")) ==
        "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59c" ++
        "faea9ea9076ede7f4af152e8b2fa9cb6"),
    ("hmac-sha512 with a 20-byte key",
      hex (hmac .sha512 (repeated 0x0b 20) (bytesOf "Hi There")) ==
        "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde" ++
        "daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"),
    ("hmac-sha256 with a short key",
      hex (hmac .sha256 (bytesOf "Jefe") (bytesOf "what do ya want for nothing?")) ==
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
    ("hmac-sha384 with a short key",
      hex (hmac .sha384 (bytesOf "Jefe") (bytesOf "what do ya want for nothing?")) ==
        "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e" ++
        "8e2240ca5e69e2c78b3239ecfab21649"),
    ("hmac-sha512 with a short key",
      hex (hmac .sha512 (bytesOf "Jefe") (bytesOf "what do ya want for nothing?")) ==
        "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea250554" ++
        "9758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"),
    ("hmac-sha256 with a full-block key",
      hex (hmac .sha256 (repeated 0xaa 20) (repeated 0xdd 50)) ==
        "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
    ("hmac-sha384 with a full-block key",
      hex (hmac .sha384 (repeated 0xaa 20) (repeated 0xdd 50)) ==
        "88062608d3e6ad8a0aa2ace014c8a86f0aa635d947ac9febe83ef4e55966144b" ++
        "2a5ab39dc13814b94e3ab6e101a34f27"),
    ("hmac-sha512 with a full-block key",
      hex (hmac .sha512 (repeated 0xaa 20) (repeated 0xdd 50)) ==
        "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39" ++
        "bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb"),
    ("hmac-sha256 with an oversized key",
      hex (hmac .sha256 (repeated 0xaa 131) (bytesOf oversizedKeyMessage)) ==
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
    ("hmac-sha384 with an oversized key",
      hex (hmac .sha384 (repeated 0xaa 131) (bytesOf oversizedKeyMessage)) ==
        "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c6" ++
        "0c2ef6ab4030fe8296248df163f44952"),
    ("hmac-sha512 with an oversized key",
      hex (hmac .sha512 (repeated 0xaa 131) (bytesOf oversizedKeyMessage)) ==
        "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f352" ++
        "6b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"),
    ("hmac-sha256 with an oversized key and a long message",
      hex (hmac .sha256 (repeated 0xaa 131) (bytesOf longMessage)) ==
        "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"),
    ("hmac-sha384 with an oversized key and a long message",
      hex (hmac .sha384 (repeated 0xaa 131) (bytesOf longMessage)) ==
        "6617178e941f020d351e2f254e8fd32c602420feb0b8fb9adccebb82461e99c5" ++
        "a678cc31e799176d3860e6110c46523e"),
    ("hmac-sha512 with an oversized key and a long message",
      hex (hmac .sha512 (repeated 0xaa 131) (bytesOf longMessage)) ==
        "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944" ++
        "b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58") ]


end Tests.Vectors
