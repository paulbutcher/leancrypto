/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Base64Url

/-!
The inputs the base64url decoder must refuse.

`Tests.Encodings` proves that every accepted string is the encoding of what it returns, which
settles all of these at once for all inputs. They are written out anyway, one per refusal, because
the general theorem says which strings are refused only through `encode`, and a reader wanting to
know whether `"Zg=="` is accepted should not have to work out what `encode` can produce.

These reduce in the kernel, so they are theorems rather than entries in the runtime suite.
-/

namespace Tests.Base64UrlCodec
open Leancrypto.Codec.Base64Url

/--
Padding is refused. Base64url as JOSE and the other users of it write it is unpadded, so a `=` means
the value came from the padded codec or from a producer that did not know the difference, and
accepting it would give one byte string two spellings that a signature cannot distinguish between.

`"Zg=="` and `"Zm9="` are the padded spellings of one and two bytes, and `"Zg="` is a single pad
character; each is required to be `none`. `=` is not in this alphabet, so `decodeChar` answers
`none` for it and the refusal needs no rule of its own, but the padded forms are the ones a caller
is most likely to be handed, so they are the ones written here.
-/
theorem reject_padding :
    decodeString "Zg==" = none ∧ decodeString "Zm9=" = none ∧ decodeString "Zg=" = none := by
  refine ⟨rfl, rfl, rfl⟩

/--
The standard alphabet is refused here, as this one is refused there. The two alphabets differ in
exactly two characters, and a decoder accepting both would hide which of the codecs a producer used,
which is the difference between a value that is safe in a URL and one that is not.

`+` is 62 in the standard alphabet and `/` is 63, and `"a+b_"` and `"a_b/"` each put one of them in
a group that is otherwise this codec's own; both are required to be `none`. Mixing rather than
isolating the foreign character is deliberate: it shows the refusal is of the character and not of
the group's shape.
-/
theorem reject_base64 : decodeString "a+b_" = none ∧ decodeString "a_b/" = none := by
  refine ⟨rfl, rfl⟩

/--
A character outside the alphabet is refused rather than skipped or folded onto a nearby value.
Nothing is stripped before decoding here, not even line endings, because unlike a PEM body a token
field arrives on one line and a decoder that tolerated breaks would accept a value with a break
inserted anywhere.

`"Zm9 v"` puts a space inside a group, `"Zm9$"` ends one with punctuation, and `"Zm9\nv"` puts in a
line break; each is required to be `none`. The last is the one worth having: `Leancrypto.Codec.Base64`
drops line endings before decoding and this codec does not, so it says the two decoders differ where
they are meant to.
-/
theorem reject_outside_alphabet :
    decodeString "Zm9 v" = none ∧ decodeString "Zm9$" = none ∧ decodeString "Zm9\nv" = none := by
  refine ⟨rfl, rfl, rfl⟩

/--
An input of length `4n + 1` is refused. No number of bytes encodes to a single trailing character:
one byte is two characters and two bytes are three, so a lone character at the end means the value
was truncated in transit, and a decoder returning what it could would hand back a prefix of a key as
though it were the key.

`"Z"` is such an input at the shortest length and `"Zm9vY"` is a full group followed by one
character; both are required to be `none`. These are the two places `decode`'s match reaches its
one-character arm, at the start of the input and after any number of full groups.
-/
theorem reject_bad_length : decodeString "Z" = none ∧ decodeString "Zm9vY" = none := by
  refine ⟨rfl, rfl⟩

/--
A final group whose bits beyond the encoded bytes are not zero is refused, so a byte string has
exactly one accepted encoding. Accepting these would give one value several spellings, and a token
signed under one of them would carry a signature over the others.

`"Zh"` spells the same single byte as `"Zg"` with a bit set that the encoder never sets, and `"Zm9"`
differs from `"Zm8"` the same way in the two-byte case; the conditions violated are the
`s1 % 16 == 0` of `oneByte` and the `s2 % 4 == 0` of `twoBytes`. Both are required to be `none`, and
the strings they are one bit away from are required to decode, so the refusal is of the spare bits
rather than of the shape.
-/
theorem reject_non_canonical :
    decodeString "Zh" = none
      ∧ decodeString "Zm9" = none
      ∧ decodeString "Zg" = some ⟨#[0x66]⟩
      ∧ decodeString "Zm8" = some ⟨#[0x66, 0x6f]⟩ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Tests.Base64UrlCodec
