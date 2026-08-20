/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Codec.Base64

/-!
The vectors of RFC 4648 §10, and the inputs a decoder must refuse.

These reduce in the kernel, so they are theorems rather than entries in the runtime suite. The
round trip itself is proved for all inputs in `Tests.Encodings`; what is checked here is agreement
with the published spelling, which no round-trip proof establishes.
-/

namespace Tests.Base64Codec
open Codec.Base64

/-- The projection rather than `String.toUTF8`, which core does not expose, so that the vectors
below still reduce in the kernel. The two are the same bytes: `toUTF8` is defined as this
projection. -/
private def utf8 (s : String) : ByteArray := s.toByteArray

theorem encode_rfc4648 :
    encodeString (utf8 "") = ""
      ∧ encodeString (utf8 "f") = "Zg=="
      ∧ encodeString (utf8 "fo") = "Zm8="
      ∧ encodeString (utf8 "foo") = "Zm9v"
      ∧ encodeString (utf8 "foob") = "Zm9vYg=="
      ∧ encodeString (utf8 "fooba") = "Zm9vYmE="
      ∧ encodeString (utf8 "foobar") = "Zm9vYmFy" := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem decode_rfc4648 :
    decodeString "" = some (utf8 "")
      ∧ decodeString "Zg==" = some (utf8 "f")
      ∧ decodeString "Zm8=" = some (utf8 "fo")
      ∧ decodeString "Zm9v" = some (utf8 "foo")
      ∧ decodeString "Zm9vYg==" = some (utf8 "foob")
      ∧ decodeString "Zm9vYmE=" = some (utf8 "fooba")
      ∧ decodeString "Zm9vYmFy" = some (utf8 "foobar") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A PEM body arrives wrapped at 64 columns, in either line ending. -/
theorem decode_wrapped :
    decodeString "Zm9v\nYmFy" = some (utf8 "foobar")
      ∧ decodeString "Zm9v\r\nYmFy" = some (utf8 "foobar")
      ∧ decodeString "Zm9vYmFy\n" = some (utf8 "foobar") := by
  refine ⟨rfl, rfl, rfl⟩

/-- The base64url alphabet is refused rather than decoded, so that a caller cannot hand a value
to the wrong one of the two codecs and get bytes back. `_` is 63 there and `-` is 62; both would
decode if the alphabets were merged. -/
theorem reject_base64url : decodeString "-_8=" = none ∧ decodeString "a-b=" = none := by
  refine ⟨rfl, rfl⟩

theorem reject_bad_length : decodeString "Zg=" = none ∧ decodeString "Zm9vY" = none := by
  refine ⟨rfl, rfl⟩

theorem reject_misplaced_padding :
    decodeString "Zg==Zg==" = none
      ∧ decodeString "=Zg=" = none
      ∧ decodeString "Z=g=" = none
      ∧ decodeString "====" = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem reject_outside_alphabet :
    decodeString "Zm9 v" = none ∧ decodeString "Zm9$" = none ∧ decodeString "Zg.=" = none := by
  refine ⟨rfl, rfl, rfl⟩

/-- `Zh==` spells the same byte as `Zg==` with a bit set that the encoder never sets. Accepting it
would give one byte string two encodings, which is the reason `Codec.Base64Url` refuses the same
shape. -/
theorem reject_non_canonical : decodeString "Zh==" = none ∧ decodeString "Zm9=" = none := by
  refine ⟨rfl, rfl⟩

end Tests.Base64Codec
