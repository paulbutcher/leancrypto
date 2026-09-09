/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Hex

/-!
What a consumer putting a digest into a signature depends on: the encoding round-trips, it emits
two characters per byte so a leading zero cannot vanish, it emits lowercase, and it accepts nothing
but its own output with the case folded.
-/

namespace Tests.HexCodec
open Leancrypto.Codec.Hex

/--
Every value a nibble can take survives being written as a character and read back. The whole hex
round trip is reduced to this fact about single characters, so it is where the alphabet is actually
checked rather than assumed from the literal.

`List.range 16` is `0` through `15`, exactly the values four bits can take, so the quantifier misses
none of them and admits nothing else. `encodeNibble n` is the character at position `n` of `digits`,
and `decodeChar` lowercases a character and searches `digits` for it, answering with its index; the
equation says that index is `n` again. `decide` evaluates all sixteen cases, which also rules out a
repeated character in `digits`, since a duplicate would send `findIdx?` to the earlier index.
-/
private theorem nibble_roundTrip : ∀ n ∈ List.range 16, decodeChar (encodeNibble n) = some n := by
  decide

/--
The character round trip in the form the proofs use, taking a bound rather than membership of a
list. Every call site already has `n < 16` from `omega`, so stating it this way keeps the conversion
in one place instead of at each use.

`h : n < 16` is what `List.mem_range` turns into `n ∈ List.range 16`, and the conclusion is
`nibble_roundTrip`'s body at that `n`. So this is the same fact restated, not a second one, and the
implicit `n` lets a rewrite supply it by unification.
-/
private theorem nr {n : Nat} (h : n < 16) : decodeChar (encodeNibble n) = some n :=
  nibble_roundTrip n (List.mem_range.mpr h)

/--
Encoding a nibble produces one of the sixteen digit characters, never the `'?'` that `getD` falls
back to. This is what connects the encoder to the alphabet: lowercase is a property of `digits`, and
`encode_lower` can appeal to it only once the encoder is known never to leave it.

`List.range 16` again covers exactly the four-bit values, and `encodeNibble n ∈ digits` says the
character produced is one of the sixteen in that list. The fallback character is not in `digits`, so
an index out of range would falsify the statement rather than be quietly admitted by it. `decide`
checks all sixteen cases.
-/
private theorem nibble_mem : ∀ n ∈ List.range 16, encodeNibble n ∈ digits := by decide

/--
Membership of the alphabet in the form the proofs use, taking a bound rather than membership of a
list. As with `nr`, this exists so that each use site can hand over the `omega` bound it already
has.

`h : n < 16` transports to `n ∈ List.range 16` by `List.mem_range`, and the conclusion is
`nibble_mem`'s body at that `n`; the fact is unchanged, only the shape of its hypothesis.
-/
private theorem nm {n : Nat} (h : n < 16) : encodeNibble n ∈ digits :=
  nibble_mem n (List.mem_range.mpr h)

/--
The alphabet is already lowercase. Nothing that emits only alphabet characters can then emit an
uppercase one, which is how the encoder's case is settled without reasoning about the encoder at
all.

`digits` is the sixteen characters `0` to `9` and `a` to `f`, and `c.toLower = c` says lowercasing
is the identity on a character, which is what "not uppercase" means here. The quantifier ranges over
the alphabet as written, so a stray uppercase letter in the literal would falsify it rather than
escape it; `decide` evaluates all sixteen.
-/
private theorem digits_lower : ∀ c ∈ digits, c.toLower = c := by decide

/--
The unfolding of `decode` at a list of two or more characters, as a rewrite rule. `decode` matches
on lists of three different shapes, so unfolding it through the equation lemmas costs an attempt
against every shape at each step; this replaces that with a single rewrite.

The left is `decode` applied to a list with at least two elements, `rest` arbitrary. The right is
that arm of the definition written out: it decodes `x`, decodes `y`, decodes `rest`, and gives
`some` of the byte `high * 16 + low` in front of the decoded tail only when all three succeed,
`none` otherwise. `rfl` closes it, so the two sides are the same term by definition and the lemma
carries no assumption of its own.
-/
private theorem decode_cons (x y : Char) (rest : List Char) :
    decode (x :: y :: rest) =
    match decodeChar x, decodeChar y, decode rest with
    | some high, some low, some tail => some (UInt8.ofNat (high * 16 + low) :: tail)
    | _, _, _ => none := rfl

/--
Hex encoding loses nothing: every byte string is recovered from its own encoding. A digest written
out and read back is the digest that was written, for every input rather than for the lengths a
vector suite happens to contain.

`encode bytes` is the character list and `decode` returns `Option (List UInt8)`, so `some bytes`
says decoding succeeds and returns the input unchanged; the quantifier is over every
`bytes : List UInt8`, the empty list included, which is the base case of the induction. It says
nothing in the other direction: character lists the encoder never produces are outside the claim, so
this is not an injectivity statement about `decode`.
-/
theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    have hb : b.toNat < 256 := b.toNat_lt_size
    simp only [encode, decode_cons, nr (show b.toNat / 16 < 16 by omega),
      nr (show b.toNat % 16 < 16 by omega), ih,
      show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat by omega, UInt8.ofNat_toNat]

/--
Encoding is exactly two characters per byte, so a byte below sixteen is written with its leading
zero rather than as a single character. A consumer that concatenates fields, or takes a digest out
of a longer string by offset, depends on that width being fixed; a signature computed over hex that
lost a leading zero fails with a mismatch that says nothing about the cause.

`(encode bytes).length` counts the characters emitted and `bytes.length` counts the bytes given, and
the equation fixes the first at twice the second. It is quantified over every input rather than over
a range of lengths, so no input is short or long enough to escape it, and the empty list gives
`0 = 2 * 0` rather than an exception.
-/
theorem length_encode (bytes : List UInt8) : (encode bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    simp only [encode, List.length_cons, ih]
    omega

/--
Encoding emits lowercase only. A request signed over uppercase hex fails against a verifier that
hashed lowercase, and the resulting mismatch says nothing about which of the two spellings was at
fault, so this is worth establishing rather than reading off the alphabet literal.

`c ∈ encode bytes` ranges over the characters the encoder actually emits for the given input, and
`c.toLower = c` holds of a character that is not uppercase. The statement is vacuous only at
`bytes = []`, where the encoder emits nothing; for every other input the membership is inhabited,
and the induction discharges those characters through `nm` and `digits_lower`.
-/
theorem encode_lower (bytes : List UInt8) : ∀ c ∈ encode bytes, c.toLower = c := by
  induction bytes with
  | nil => intro c hc; simp only [encode, List.not_mem_nil] at hc
  | cons b rest ih =>
    intro c hc
    have hb : b.toNat < 256 := b.toNat_lt_size
    simp only [encode, List.mem_cons] at hc
    rcases hc with h | h | h
    · subst h; exact digits_lower _ (nm (by omega))
    · subst h; exact digits_lower _ (nm (by omega))
    · exact ih c h

/--
A character the decoder accepts is the one the encoder writes for the nibble it answers with, up to
case. Everything the canonicity theorem below says about which strings are refused rests on this,
and the `toLower` in it is where this decoder's one liberty appears.

`decodeChar c = some n` says searching `digits` for `c.toLower` found it at position `n`. The
conclusion is that `n` is a nibble value, below 16, and that `encodeNibble n`, the character at
position `n`, is `c.toLower`. It is not `c`, and cannot be: `decodeChar` folds case before
searching, so `'A'` and `'a'` both answer `some 10` and only one of them is what the encoder writes.
-/
private theorem decodeChar_sound {c : Char} {n : Nat} (h : decodeChar c = some n) :
    n < 16 ∧ encodeNibble n = c.toLower := by
  rw [decodeChar, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hn, hp, -⟩ := h
  exact ⟨hn, by simpa [encodeNibble, List.getElem?_eq_getElem hn] using hp⟩

/--
Every character list the decoder accepts is the encoding of what it hands back, once case is folded.
That is the strongest form the claim takes for this codec, and the residue is exactly the liberty
`decodeChar` documents: two accepted strings that decode to the same bytes differ only in the case
of their letters, never in a character, a length, or a digit. A string with an odd length, or with
any character outside the alphabet, is not `encode` of anything and so is refused.

`decode cs = some bs` is the decoder succeeding on `cs` and answering `bs`. `cs.map Char.toLower` is
`cs` with its letters folded down, and the conclusion says `encode bs` is exactly that, character
for character; with `encode_lower`, which says the encoder writes no uppercase, the two sides are
lists of the same lowercase characters. The induction is over `decode.induct`, so the cases are the
decoder's arms, the odd-length one included, where the hypothesis is contradictory.
-/
theorem encode_decode (cs : List Char) (bs : List UInt8) (h : decode cs = some bs) :
    encode bs = cs.map Char.toLower := by
  induction cs using decode.induct generalizing bs with
  | case1 => simp [decode] at h; subst h; rfl
  | case2 c => simp [decode] at h
  | case3 x y rest high low tail hrest hy hx ih =>
    obtain ⟨hhigh, hx'⟩ := decodeChar_sound hx
    obtain ⟨hlow, hy'⟩ := decodeChar_sound hy
    rw [decode_cons, hx, hy, hrest] at h
    obtain rfl : bs = UInt8.ofNat (high * 16 + low) :: tail := (Option.some.inj h).symm
    simp only [encode, List.map_cons,
      show (UInt8.ofNat (high * 16 + low)).toNat = high * 16 + low by
        simp [Nat.mod_eq_of_lt (show high * 16 + low < 256 by omega)]]
    rw [show (high * 16 + low) / 16 = high by omega,
      show (high * 16 + low) % 16 = low by omega, hx', hy', ih tail hrest]
  | case4 x y rest hno ih =>
    rw [decode_cons] at h
    split at h
    · exact (hno _ _ _ ‹_› ‹_› ‹_›).elim
    · simp at h


/--
An input of odd length is refused. Every byte is two characters, so an odd count means a character
was lost or added in transit, and a decoder that dropped the odd one would turn a damaged digest
into a shorter digest rather than into an error.

`"a"` is such an input at the shortest length and `"abc"` is a whole byte followed by one character;
both are required to be `none`. These are the two places `decode`'s match reaches its
single-character arm, at the start of the input and after any number of complete pairs.
-/
theorem reject_odd_length : decodeString "a" = none ∧ decodeString "abc" = none := by
  refine ⟨rfl, rfl⟩

/--
A character outside the alphabet is refused rather than skipped or folded onto a nearby digit.
Nothing is stripped before decoding, so a separator a person inserted for legibility is an error
here, which it must be: a digest is compared byte for byte and a decoder that ignored punctuation
would accept several spellings of one value.

`"ab cd"` puts a space between two bytes, `"ab:cd"` a separator of the kind a fingerprint is often
written with, `"abcg"` a letter one past the end of the alphabet, and `"12x4"` one in the middle of
a byte; each is required to be `none`. The `g` is the one worth having, since it is the character an
alphabet extended by one would admit.
-/
theorem reject_outside_alphabet :
    decodeString "ab cd" = none
      ∧ decodeString "ab:cd" = none
      ∧ decodeString "abcg" = none
      ∧ decodeString "12x4" = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/--
Case is the one thing the decoder does fold, and it folds it completely. This is stated rather than
left implicit because it is the whole residue of `encode_decode`: two accepted strings that decode
to the same bytes differ in the case of their letters and in nothing else, so a consumer that needs
one spelling per value must compare the encoding rather than the input it was given.

The three strings are the same two bytes written in lowercase, uppercase, and a mixture, and each is
required to decode to those bytes. `decodeChar` calls `Char.toLower` before searching the alphabet,
which is why all three succeed; `encode_lower` says the encoder emits only the first of them.
-/
theorem accept_either_case :
    decodeString "abcd" = some ⟨#[0xab, 0xcd]⟩
      ∧ decodeString "ABCD" = some ⟨#[0xab, 0xcd]⟩
      ∧ decodeString "AbCd" = some ⟨#[0xab, 0xcd]⟩ := by
  refine ⟨rfl, rfl, rfl⟩


end Tests.HexCodec
