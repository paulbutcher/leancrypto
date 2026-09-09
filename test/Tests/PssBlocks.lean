/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Rsa.Pss
import Tests.Cavp

/-!
The four rejections in `EMSA-PSS-VERIFY` that no published vector reaches, because a signer does
not produce a block with one field wrong. A lenient verifier agrees with every positive vector in
`Tests.PssCavp` and with most of the negative ones, and is caught only here.

The block is not constructed. It is the one recovered from the first passing SHA-256 case of
`SigVerPSS_186-3.rsp`, so the starting point is a signature NIST published rather than something
this library's own encoder produced, and each check below damages exactly one field of it.

A damaged byte of the masked `DB` is a damaged byte of `DB`, because the two differ by a mask that
does not depend on them. So flipping the low bit of a masked byte flips the low bit of the byte it
covers, which is how the separator and the zero run are reached from outside the mask.
-/

namespace Tests.PssBlocks
open Leancrypto Tests.Cavp

private def modulus : String :=
  "a47d04e7cacdba4ea26eca8a4c6e14563c2ce03b623b768c0d49868a57121301" ++
  "dbf783d82f4c055e73960e70550187d0af62ac3496f0a3d9103c2eb7919a7275" ++
  "2fa7ce8c688d81e3aee99468887a15288afbb7acb845b7c522b5c64e678fcd3d" ++
  "22feb84b44272700be527d2b2025a3f83c2383bf6a39cf5b4e48b3cf2f56eef0" ++
  "dfff18555e31037b915248694876f3047814415164f2c660881e694b58c28038" ++
  "a032ad25634aad7b39171dee368e3d59bfb7299e4601d4587e68caaf8db457b7" ++
  "5af42fc0cf1ae7caced286d77fac6cedb03ad94f1433d2c94d08e60bc1fdef05" ++
  "43cd2951e765b38230fdd18de5d2ca627ddc032fe05bbd2ff21e2db1c2f94d8b"

private def exponent : String := "10e43f"

private def message : String :=
  "e002377affb04f0fe4598de9d92d31d6c786040d5776976556a2cfc55e54a1dc" ++
  "b3cb1b126bd6a4bed2a184990ccea773fcc79d246553e6c64f686d21ad415267" ++
  "3cafec22aeb40f6a084e8a5b4991f4c64cf8a927effd0fd775e71e8329e41fdd" ++
  "4457b3911173187b4f09a817d79ea2397fc12dfe3d9c9a0290c8ead31b6690a6"

private def signature : String :=
  "4f9b425c2058460e4ab2f5c96384da2327fd29150f01955a76b4efe956af06dc" ++
  "08779a374ee4607eab61a93adc5608f4ec36e47f2a0f754e8ff839a8a19b1db1" ++
  "e884ea4cf348cd455069eb87afd53645b44e28a0a56808f5031da5ba9112768d" ++
  "fbfca44ebe63a0c0572b731d66122fb71609be1480faa4e4f75e43955159d70f" ++
  "081e2a32fbb19a48b9f162cf6b2fb445d2d6994bc58910a26b5943477803cdaa" ++
  "a1bd74b0da0a5d053d8b1dc593091db5388383c26079f344e2aea600d0e32416" ++
  "4b450f7b9b465111b7265f3b1b063089ae7e2623fc0fda8052cf4bf3379102fb" ++
  "f71d7c98e8258664ceed637d20f95ff0111881e650ce61f251d9c3a629ef222d"

private def key : Rsa.PublicKey :=
  { modulus := natOfHex modulus, exponent := natOfHex exponent }

/-- The block the signature recovers, at the width RFC 8017 §8.1.2 gives it: one bit narrower than
the modulus, which for a 2048-bit modulus is still 256 bytes and leaves one unused leading bit. -/
private def block : ByteArray :=
  Rsa.bytesOfNat 256 (Rsa.powMod (natOfHex signature) key.exponent key.modulus)

private def emBits : Nat := 2047

private def saltLength : Nat := 32

/-- `DB` is 223 bytes: 190 zeros, the `0x01`, then the 32 bytes of salt. -/
private def separatorIndex : Nat := 190

private def damaged (index : Nat) (change : UInt8 → UInt8) : ByteArray :=
  ⟨block.data.modify index change⟩

private def accepts (em : ByteArray) : Bool :=
  Rsa.Pss.verifyEncoded .sha256 saltLength emBits (bytesOfHex message) em

public def checks : List (String × Bool) :=
  [ ("the recovered block is accepted as it stands", accepts block),
    ("a block whose trailer is not 0xbc is refused",
      accepts (damaged 255 fun _ => 0xbb) == false),
    ("a block with an unused leading bit set is refused",
      accepts (damaged 0 (· ||| 0x80)) == false),
    ("a block whose separator is not 0x01 is refused",
      accepts (damaged separatorIndex (· ^^^ 0x01)) == false),
    ("a block with a non-zero byte before the separator is refused",
      accepts (damaged 100 (· ^^^ 0x01)) == false),
    -- Not one of the four, but it is what the other four exist to protect: the digest itself.
    ("a block whose salt has been altered is refused",
      accepts (damaged (separatorIndex + 1) (· ^^^ 0x01)) == false) ]

end Tests.PssBlocks
