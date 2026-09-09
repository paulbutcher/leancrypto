/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Base64

/-!
The vectors of RFC 4648 §10, and the inputs a decoder must refuse.

These reduce in the kernel, so they are theorems rather than entries in the runtime suite. The
round trip itself is proved for all inputs in `Tests.Encodings`; what is checked here is agreement
with the published spelling, which no round-trip proof establishes.
-/

namespace Tests.Base64Codec
open Leancrypto.Codec.Base64

/-- The projection rather than `String.toUTF8`, which core does not expose, so that the vectors
below still reduce in the kernel. The two are the same bytes: `toUTF8` is defined as this
projection. -/
private def utf8 (s : String) : ByteArray := s.toByteArray

/--
The encoder produces the spelling RFC 4648 §10 publishes, across the whole ladder of input lengths.
No round-trip proof establishes this: an encoder over a permuted alphabet round-trips perfectly and
agrees with nobody, and a PEM body written in such an alphabet would be read as a different key
everywhere else.

The seven conjuncts are the RFC's vectors, the empty string through `"foobar"`, taken as UTF-8 bytes
by `utf8` and encoded; each right-hand side is the RFC's own string, character for character, with
the `=` padding it publishes for the inputs whose length is not a multiple of three. The lengths run
from 0 to 6, so every residue of the group size appears, and twice over apart from the empty case.
Each conjunct is closed by `rfl`, so the agreement is by reduction in the kernel rather than by
running the encoder.
-/
theorem encode_rfc4648 :
    encodeString (utf8 "") = ""
      ∧ encodeString (utf8 "f") = "Zg=="
      ∧ encodeString (utf8 "fo") = "Zm8="
      ∧ encodeString (utf8 "foo") = "Zm9v"
      ∧ encodeString (utf8 "foob") = "Zm9vYg=="
      ∧ encodeString (utf8 "fooba") = "Zm9vYmE="
      ∧ encodeString (utf8 "foobar") = "Zm9vYmFy" := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
The decoder returns the bytes the RFC's vectors stand for, on the same ladder of lengths. With
`encode_rfc4648` this pins both directions to the published spelling; pinned only to each other they
could agree perfectly on an alphabet nobody else uses.

Each conjunct decodes one of the RFC's strings and requires `some` of the corresponding bytes, so a
decoder that answered `none`, or that returned different bytes, fails; the padded vectors carry
their `=` characters exactly as published. The claim is about these seven inputs alone. That every
encoding decodes is `Tests.Encodings.Base64.decode_encode`, and neither statement implies the other.
-/
theorem decode_rfc4648 :
    decodeString "" = some (utf8 "")
      ∧ decodeString "Zg==" = some (utf8 "f")
      ∧ decodeString "Zm8=" = some (utf8 "fo")
      ∧ decodeString "Zm9v" = some (utf8 "foo")
      ∧ decodeString "Zm9vYg==" = some (utf8 "foob")
      ∧ decodeString "Zm9vYmE=" = some (utf8 "fooba")
      ∧ decodeString "Zm9vYmFy" = some (utf8 "foobar") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
A base64 body that arrives wrapped across lines decodes to the same bytes as one that does not. PEM
wraps at 64 columns, so a decoder without this would push line-stripping onto every caller, and one
caller would eventually forget.

The three conjuncts wrap `"Zm9vYmFy"` with a bare line feed, with a carriage return and line feed,
and with a trailing line feed after the whole value; each is required to give
`some (utf8 "foobar")`, the same bytes the unwrapped string gives in `decode_rfc4648`. The two line
endings are the two in use, so neither a Unix-wrapped nor a DOS-wrapped PEM is left to assumption,
and the third covers the newline a file ends with.
-/
theorem decode_wrapped :
    decodeString "Zm9v\nYmFy" = some (utf8 "foobar")
      ∧ decodeString "Zm9v\r\nYmFy" = some (utf8 "foobar")
      ∧ decodeString "Zm9vYmFy\n" = some (utf8 "foobar") := by
  refine ⟨rfl, rfl, rfl⟩

/--
The base64url alphabet is refused here rather than decoded, so that a caller cannot hand a value to
the wrong one of the two codecs and get bytes back. A decoder accepting both alphabets would hide
which one the producer used, and the two disagree on exactly the characters below.

`_` is 63 in base64url and `-` is 62, and both would decode if the alphabets were merged. `"-_8="`
is a well-formed base64url final group, and `"a-b="` puts a single foreign character in a group that
is otherwise this codec's own; both are required to be `none`, so the refusal cannot be an accident
of length or of padding.
-/
theorem reject_base64url : decodeString "-_8=" = none ∧ decodeString "a-b=" = none := by
  refine ⟨rfl, rfl⟩

/--
An input whose length is not a multiple of four is refused. Padded base64 has no partial group, so
such a length means the value was truncated in transit, and a decoder returning what it could would
hand its caller a prefix of a key as though it were a key.

`"Zg="` is a final group one character short, and `"Zm9vY"` is a complete group followed by a single
character; both are required to be `none`. The two are the shapes that arise at the end of a short
input and at the start of a fresh group, which are the two places `decode`'s match falls through to
its catch-all arm.
-/
theorem reject_bad_length : decodeString "Zg=" = none ∧ decodeString "Zm9vY" = none := by
  refine ⟨rfl, rfl⟩

/--
Padding is accepted only where it belongs, at the end of the final group. Padding anywhere earlier
is what would let one byte string be spelled many ways, since everything after it would be ignored
by a decoder that stopped at the first `=`.

`"Zg==Zg=="` puts a complete padded group in front of another group; `"=Zg="` and `"Z=g="` put a pad
character at the first and the second position of a group that is also padded at the end; and
`"===="` is nothing but padding. Each is required to be `none`. `decodeChar pad` is `none`, so all
four are refused by `fullGroup` and `finalGroup` decoding the characters they are handed, without a
rule dedicated to misplaced padding that could be got round.
-/
theorem reject_misplaced_padding :
    decodeString "Zg==Zg==" = none
      ∧ decodeString "=Zg=" = none
      ∧ decodeString "Z=g=" = none
      ∧ decodeString "====" = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/--
A character outside the alphabet is refused rather than skipped or folded onto a nearby value. Only
line endings are dropped before decoding; anything else must be a base64 character or the input was
not base64, and skipping it would let two different strings decode to one value.

`"Zm9 v"` puts a space inside a group, `"Zm9$"` ends one with punctuation, and `"Zg.="` puts a
foreign character where padding would otherwise begin; each is required to be `none`. The space is
the one worth having: it is whitespace, and `keep` drops only `\n` and `\r`, so a decoder that
stripped whitespace in general would fail here.
-/
theorem reject_outside_alphabet :
    decodeString "Zm9 v" = none ∧ decodeString "Zm9$" = none ∧ decodeString "Zg.=" = none := by
  refine ⟨rfl, rfl, rfl⟩

/--
A final group whose bits beyond the encoded bytes are not zero is refused, so a byte string has
exactly one accepted encoding. Accepting these would give one value several spellings, and a store
keyed on the digest of a spelling would then hold one value under several keys.

`"Zh=="` spells the same single byte as `"Zg=="` with a bit set that the encoder never sets, and
`"Zm9="` differs from `"Zm8="` the same way in the two-byte case; the conditions violated are the
`s1 % 16 == 0` of `oneByte` and the `s2 % 4 == 0` of `twoBytes`. Both are required to be `none`,
which is the shape `Leancrypto.Codec.Base64Url` refuses for the same reason.
-/
theorem reject_non_canonical : decodeString "Zh==" = none ∧ decodeString "Zm9=" = none := by
  refine ⟨rfl, rfl⟩

end Tests.Base64Codec
