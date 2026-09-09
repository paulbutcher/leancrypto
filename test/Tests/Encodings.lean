/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Base32
import Leancrypto.Codec.Base64
import Leancrypto.Codec.Base64Url

/-!
Round-trip theorems for the three encodings, and canonicity theorems for two of them.

The round trip says nothing is lost; canonicity says nothing else is accepted, which is the half a
consumer needs against an input an attacker wrote. Crockford base32 has no canonicity theorem
because it is false of that decoder by design: the decoder folds case and the substitutions a
person makes when transcribing, so a byte string has several spellings it will read.

Two shapes here are for elaboration cost rather than clarity, and both matter: the file is
minutes slower without them. `decode` is unfolded through `rfl` lemmas, because applying the
equation lemmas of a match over list literals of several lengths is expensive. And the
character-level rewrites are packaged into one lemma per group, stated over quintet variables,
so that the group values appear in a rewrite only after unification has already fixed them;
rewriting under `simp` with the arithmetic in place makes every failed match an attempt to
unfold the alphabet.
-/

namespace Tests.Encodings

/--
A natural below 256 survives being made into a byte. The round-trip theorems run from bytes to
characters and never need this; the canonicity theorems run the other way, and every byte they
produce is assembled from sextets whose values have to be read back out of it afterwards.

`h : v < 256` is the range a `UInt8` holds, `UInt8.ofNat` truncates to that range, and `.toNat`
reads the result back; the equation says the truncation did nothing. Above 256 the statement would
be false rather than vacuous, so the hypothesis carries the weight, and it is discharged at each
use site from the bounds on the sextets that built the byte.
-/
private theorem toNat_ofNat {v : Nat} (h : v < 256) : (UInt8.ofNat v).toNat = v := by
  simp [Nat.mod_eq_of_lt h]

namespace Base32
open Leancrypto.Codec.Base32

/--
Every value five bits can take survives being written as a Crockford character and read back. The
round trip for whole byte lists is reduced to this fact about single characters, so this is where
the alphabet, and the liberties the decoder takes with it, are actually checked.

`List.range 32` is `0` through `31`, exactly the quintet values, so nothing in range is missed and
nothing else is admitted. `encodeQuintet n` is the character at position `n` of `alphabet`, and
`decodeChar` canonicalises a character before searching, folding case and mapping `I` and `L` onto
`1` and `O` onto `0`; the equation says the index it finds is `n` again. `decide` evaluates all
thirty-two, so those substitutions are checked not to collide with a character the encoder emits.
-/
private theorem quintet_roundTrip : ∀ n ∈ List.range 32, decodeChar (encodeQuintet n) = some n := by
  decide

/--
The character round trip in the form the group lemmas use, taking a bound rather than membership of
a list. Every use site has `n < 32` from `omega` already, and there are some thirty of them, so the
conversion is done once here.

`h : n < 32` is what `List.mem_range` turns into `n ∈ List.range 32`, and the conclusion is
`quintet_roundTrip`'s body at that `n`; the fact is the same one, and the implicit `n` lets a
rewrite fix it by unification rather than by being told.
-/
private theorem qr {n : Nat} (h : n < 32) : decodeChar (encodeQuintet n) = some n :=
  quintet_roundTrip n (List.mem_range.mpr h)

/--
`decode` at a two-character list, as a rewrite rule. Two characters are the shortest group base32
has, carrying one byte, and reaching that arm through the equation lemmas means matching a list
literal against every one of nine.

The left is `decode [x, y]`; the right is that arm of the definition spelled out, decoding both
characters and handing the pair to `oneByte`, which is where the requirement that the two spare bits
are zero lives. `rfl` closes it, so the sides are the same term by definition and the lemma assumes
nothing of its own.
-/
private theorem decode_2 (x y : Char) : decode [x, y] =
    match decodeChar x, decodeChar y with
    | some q0, some q1 => oneByte q0 q1
    | _, _ => none := rfl

/--
`decode` at a four-character list, as a rewrite rule. Four characters carry two bytes with four bits
to spare, the widest margin of any group here.

The left is `decode [x, y, z, w]` and the right is the corresponding arm written out: all four
characters are decoded and the quintets handed to `twoBytes`, which yields bytes only when the last
quintet's low four bits are zero. `rfl` closes it; the lemma is the definition, not a claim about
it.
-/
private theorem decode_4 (x y z w : Char) : decode [x, y, z, w] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w with
    | some q0, some q1, some q2, some q3 => twoBytes q0 q1 q2 q3
    | _, _, _, _ => none := rfl

/--
`decode` at a five-character list, as a rewrite rule. Five characters carry three bytes with a
single bit to spare, the narrowest margin of any group here.

The left is `decode [x, y, z, w, v]` and the right is its arm: five characters decoded and the
quintets handed to `threeBytes`, which requires the final quintet to be even, that one spare bit
being zero. `rfl` closes it, so nothing is assumed beyond the definition.
-/
private theorem decode_5 (x y z w v : Char) : decode [x, y, z, w, v] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v with
    | some q0, some q1, some q2, some q3, some q4 => threeBytes q0 q1 q2 q3 q4
    | _, _, _, _, _ => none := rfl

/--
`decode` at a seven-character list, as a rewrite rule. Seven characters carry four bytes with three
bits to spare, the last of the partial groups.

The left is `decode` on seven characters and the right its arm: each character is decoded and the
quintets handed to `fourBytes`, which requires the last quintet's low three bits to be zero. `rfl`
closes it. Lists of three and of six characters have arms of their own answering `none`, so they
need no lemma.
-/
private theorem decode_7 (x y z w v u t : Char) : decode [x, y, z, w, v, u, t] =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6 =>
      fourBytes q0 q1 q2 q3 q4 q5 q6
    | _, _, _, _, _, _, _ => none := rfl

/--
`decode` at a full group followed by whatever comes after it, as a rewrite rule. This is the only
arm that recurses, so it is the one the induction step of the round trip turns on.

The left is `decode` on eight characters followed by an arbitrary `rest`. The right decodes those
eight and, separately, `rest`, succeeding only when all nine succeed and giving the five bytes of
the group in front of the decoded tail. `fiveBytes` carries no `Option`: forty bits are exactly five
bytes, so a full group has no spare bits to require anything of.
-/
private theorem decode_8 (x y z w v u t s : Char) (rest : List Char) :
    decode (x :: y :: z :: w :: v :: u :: t :: s :: rest) =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decodeChar v, decodeChar u,
        decodeChar t, decodeChar s, decode rest with
    | some q0, some q1, some q2, some q3, some q4, some q5, some q6, some q7, some tail =>
      some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail)
    | _, _, _, _, _, _, _, _, _ => none := rfl

/--
A two-character group of quintets known to be in range decodes to whatever `oneByte` makes of them.
Packaging both character-level rewrites into one step keeps the encoder's arithmetic out of the
matching, which is what makes this file elaborate in seconds rather than minutes.

`h0` and `h1` bound the quintets below 32, which is what `qr` needs; the conclusion decodes the two
encoded characters and gives `oneByte q0 q1` unevaluated, leaving its spare-bit condition to the
caller, where the numbers are known. `q0` and `q1` are implicit variables rather than the encoder's
expressions, so the rewrite matches on shape before any arithmetic is looked at.
-/
private theorem group1 {q0 q1 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1] = oneByte q0 q1 := by
  simp only [decode_2, qr h0, qr h1]

/--
A four-character group of in-range quintets decodes to whatever `twoBytes` makes of them; the step
behind the two-byte case of the round trip.

The four hypotheses bound the quintets below 32 for `qr`, and the conclusion rewrites `decode` of
the four encoded characters to `twoBytes q0 q1 q2 q3`, left unevaluated so that its `q3 % 16 == 0`
is discharged where the numbers are known. As in `group1` the quintets are variables, so nothing
about their values is needed to apply it.
-/
private theorem group2 {q0 q1 q2 q3 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3]
      = twoBytes q0 q1 q2 q3 := by
  simp only [decode_4, qr h0, qr h1, qr h2, qr h3]

/--
A five-character group of in-range quintets decodes to whatever `threeBytes` makes of them; the step
behind the three-byte case of the round trip.

The five hypotheses feed `qr` at each position, and the conclusion rewrites `decode` of the five
encoded characters to `threeBytes q0 q1 q2 q3 q4`, its `q4 % 2 == 0` still to be discharged. Stated
over quintet variables, it holds of any five in-range values rather than only those the encoder
produces.
-/
private theorem group3 {q0 q1 q2 q3 q4 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) (h4 : q4 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3,
      encodeQuintet q4] = threeBytes q0 q1 q2 q3 q4 := by
  simp only [decode_5, qr h0, qr h1, qr h2, qr h3, qr h4]

/--
A seven-character group of in-range quintets decodes to whatever `fourBytes` makes of them; the step
behind the four-byte case, and the widest of the partial groups.

The seven hypotheses feed `qr` at each position, and the conclusion rewrites `decode` of the seven
encoded characters to `fourBytes q0 q1 q2 q3 q4 q5 q6`, whose `q6 % 8 == 0` the caller discharges.
All seven quintets are implicit, so the rewrite fires on the shape of the list alone.
-/
private theorem group4 {q0 q1 q2 q3 q4 q5 q6 : Nat} (h0 : q0 < 32) (h1 : q1 < 32) (h2 : q2 < 32)
    (h3 : q3 < 32) (h4 : q4 < 32) (h5 : q5 < 32) (h6 : q6 < 32) :
    decode [encodeQuintet q0, encodeQuintet q1, encodeQuintet q2, encodeQuintet q3,
      encodeQuintet q4, encodeQuintet q5, encodeQuintet q6] = fourBytes q0 q1 q2 q3 q4 q5 q6 := by
  simp only [decode_7, qr h0, qr h1, qr h2, qr h3, qr h4, qr h5, qr h6]

/--
A full group of in-range quintets, in front of a character list that is known to decode, decodes to
the group's five bytes in front of that list's bytes. This is the step the induction along a byte
list runs on, so unlike the others it carries a hypothesis about what follows.

The eight bounds feed `qr`, and `hcs : decode cs = some tail` is the round trip already established
for the rest of the input. The conclusion is `some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail)` with
no condition attached, because a full group has no spare bits; `cs` and `tail` are implicit, so the
lemma applies at whatever the induction hypothesis happens to be about.
-/
private theorem group5 {q0 q1 q2 q3 q4 q5 q6 q7 : Nat} (h0 : q0 < 32) (h1 : q1 < 32)
    (h2 : q2 < 32) (h3 : q3 < 32) (h4 : q4 < 32) (h5 : q5 < 32) (h6 : q6 < 32) (h7 : q7 < 32)
    {cs : List Char} {tail : List UInt8} (hcs : decode cs = some tail) :
    decode (encodeQuintet q0 :: encodeQuintet q1 :: encodeQuintet q2 :: encodeQuintet q3
        :: encodeQuintet q4 :: encodeQuintet q5 :: encodeQuintet q6 :: encodeQuintet q7 :: cs)
      = some (fiveBytes q0 q1 q2 q3 q4 q5 q6 q7 ++ tail) := by
  simp only [decode_8, qr h0, qr h1, qr h2, qr h3, qr h4, qr h5, qr h6, qr h7, hcs]

/--
A one-byte input round-trips. Base32 spells one byte in two characters with two bits over, and this
is where those bits are shown to be zero rather than assumed.

`encode [a]` is the two-character group, and the proof rewrites with `group1` at the encoder's own
quintets, `a.toNat / 8` and `a.toNat % 8 * 4`, each below 32 for any byte. `oneByte` then needs
`a.toNat % 8 * 4 % 4 = 0`, which holds because that quintet is a multiple of four by construction,
and reassembly is `a.toNat / 8 * 8 + a.toNat % 8 * 4 / 4 = a.toNat`. The result is `some [a]`, so
nothing is lost and nothing is added.
-/
private theorem rt1 (a : UInt8) : decode (encode [a]) = some [a] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  simp only [encode]
  rw [group1 (by omega : a.toNat / 8 < 32) (by omega : a.toNat % 8 * 4 < 32), oneByte,
    show a.toNat % 8 * 4 % 4 = 0 by omega,
    show a.toNat / 8 * 8 + a.toNat % 8 * 4 / 4 = a.toNat by omega, UInt8.ofNat_toNat]
  rfl

/--
A two-byte input round-trips. Two bytes are spelled in four characters with four bits over, the most
room any group here leaves an encoder to leave something behind in.

`encode [a, b]` reads the pair as the number `a.toNat * 256 + b.toNat` and cuts four quintets out of
it; the proof rewrites with `group2` at those four expressions, each below 32 by `omega`. `twoBytes`
needs the last to be a multiple of sixteen, which it is by construction, and the two `show`
equations put the halves back together as `a.toNat` and `b.toNat`. The result is `some [a, b]`.
-/
private theorem rt2 (a b : UInt8) : decode (encode [a, b]) = some [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  simp only [encode]
  rw [group2 (by omega : (a.toNat * 256 + b.toNat) / 2048 < 32)
      (by omega : (a.toNat * 256 + b.toNat) / 64 % 32 < 32)
      (by omega : (a.toNat * 256 + b.toNat) / 2 % 32 < 32)
      (by omega : (a.toNat * 256 + b.toNat) % 2 * 16 < 32),
    twoBytes,
    show (a.toNat * 256 + b.toNat) % 2 * 16 % 16 = 0 by omega,
    show (a.toNat * 256 + b.toNat) / 2048 * 8 + (a.toNat * 256 + b.toNat) / 64 % 32 / 4
      = a.toNat by omega,
    show (a.toNat * 256 + b.toNat) / 64 % 32 % 4 * 64 + (a.toNat * 256 + b.toNat) / 2 % 32 * 2
      + (a.toNat * 256 + b.toNat) % 2 * 16 / 16 = b.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

/--
A three-byte input round-trips. Three bytes are spelled in five characters with a single bit over,
so this is the case where the encoder has least room and a mistake in the shifts would be least
visible.

`encode [a, b, c]` reads the three bytes as one number and cuts five quintets from it; `group3` is
applied at those five expressions with their `omega` bounds. `threeBytes` needs the last quintet
even, and the three `show` equations recover `a.toNat`, `b.toNat` and `c.toNat`, each byte
reassembled from the two or three quintets it straddles. The result is `some [a, b, c]`.
-/
private theorem rt3 (a b c : UInt8) : decode (encode [a, b, c]) = some [a, b, c] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  simp only [encode]
  rw [group3 (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 524288 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 512 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 < 32)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 < 32),
    threeBytes,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 % 2 = 0 by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 524288 * 8
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 / 4 = a.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16384 % 32 % 4 * 64
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 512 % 32 * 2
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 / 16 = b.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 16 % 32 % 16 * 16
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 16 * 2 / 2 = c.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

/--
A four-byte input round-trips. Four bytes are spelled in seven characters with three bits over, the
last of the partial groups and the one whose arithmetic spans the widest numbers.

`encode [a, b, c, d]` reads the four bytes as one number below `2 ^ 32` and cuts seven quintets from
it; `group4` is applied at those seven with their bounds. `fourBytes` needs the last quintet's low
three bits zero, and four `show` equations reassemble the bytes, each from the two or three quintets
it straddles. The result is `some [a, b, c, d]`.
-/
private theorem rt4 (a b c d : UInt8) : decode (encode [a, b, c, d]) = some [a, b, c, d] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  have hd : d.toNat < 256 := d.toNat_lt_size
  simp only [encode]
  rw [group4
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 134217728 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 131072 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4 % 32 < 32)
      (by omega : (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 < 32),
    fourBytes,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 % 8 = 0 by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 134217728 * 8
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 / 4
      = a.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4194304 % 32 % 4 * 64
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 131072 % 32 * 2
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 / 16
      = b.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4096 % 32 % 16 * 16
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 / 2
      = c.toNat by omega,
    show (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 128 % 32 % 2 * 128
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) / 4 % 32 * 4
      + (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) % 4 * 8 / 8
      = d.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

/--
The inductive step: five more bytes in front of a list that already round-trips still round-trips.
Five bytes are a whole group with no bits left over, which is why the encoding of a long input is
the concatenation of independent groups and the induction can be this simple.

`ih` is the round trip for `rest`, and `encode` on `a :: b :: c :: d :: e :: rest` is eight
characters followed by `encode rest`, so `group5` applies with `ih` as its hypothesis about the
tail. The eight bounds are `omega` facts about the quintets cut from the forty-bit number the five
bytes make, five `show` equations reassemble the bytes, and no spare-bit condition appears because
there are none. The result is `some (a :: b :: c :: d :: e :: rest)`.
-/
private theorem rt5 (a b c d e : UInt8) (rest : List UInt8)
    (ih : decode (encode rest) = some rest) :
    decode (encode (a :: b :: c :: d :: e :: rest)) = some (a :: b :: c :: d :: e :: rest) := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  have hd : d.toNat < 256 := d.toNat_lt_size
  have he : e.toNat < 256 := e.toNat_lt_size
  simp only [encode]
  rw [group5
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 34359738368 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 33554432 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1024 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 < 32)
      (by omega : (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) % 32 < 32) ih,
    fiveBytes,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 34359738368 * 8
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 / 4 = a.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1073741824 % 32 % 4 * 64
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 33554432 % 32 * 2
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 / 16 = b.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1048576 % 32 % 16 * 16
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 / 2 = c.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32768 % 32 % 2 * 128
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 1024 % 32 * 4
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 / 8 = d.toNat by omega,
    show (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) / 32 % 32 % 8 * 32
      + (a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 + d.toNat * 256
        + e.toNat) % 32 = e.toNat by omega]
  simp only [UInt8.ofNat_toNat, List.cons_append, List.nil_append]

/--
Crockford base32 encoding loses nothing: every byte string is recovered from its own encoding. This
is the claim the codec exists to support, and it holds for every input rather than for the lengths
some vector suite happens to contain.

`encode bytes` is the character list, `decode` returns `Option (List UInt8)`, and `some bytes` says
decoding succeeds and hands back the input unchanged, for every `bytes` including the empty list.
The induction is over `encode.induct`, so its cases are the encoder's own: the four partial groups
and the recursive one, discharged by `rt1` through `rt5`. Character lists the encoder never produces
are outside the claim, so this does not say that `decode` is injective.
-/
theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => exact rt1 a
  | case3 a b => exact rt2 a b
  | case4 a b c => exact rt3 a b c
  | case5 a b c d => exact rt4 a b c d
  | case6 a b c d e rest ih => exact rt5 a b c d e rest ih

end Base32

namespace Base64Url
open Leancrypto.Codec.Base64Url

/--
Every value six bits can take survives being written as a base64url character and read back. This
alphabet differs from the standard one in its last two characters, so the fact is established
against the alphabet in this module rather than borrowed from the other.

`List.range 64` is `0` through `63`, exactly the sextet values. `encodeSextet n` is the character at
position `n` of `alphabet`, and `decodeChar` searches the alphabet for an exact match, with no case
folding and no substitutions, answering with the index; the equation says that index is `n` again.
`decide` covers all sixty-four, which also rules out a repeat in the alphabet literal, since a
duplicate would send `findIdx?` to the earlier position.
-/
private theorem sextet_roundTrip : ∀ n ∈ List.range 64, decodeChar (encodeSextet n) = some n := by
  decide

/--
The character round trip as the group lemmas want it, taking a bound rather than membership of a
list. The bound is what `omega` produces at each use site, so the conversion belongs here rather
than at each of them.

`h : n < 64` becomes `n ∈ List.range 64` by `List.mem_range`, and the conclusion is
`sextet_roundTrip`'s body at that `n`. Nothing new is claimed; the implicit `n` is what lets a
rewrite instantiate it.
-/
private theorem sr {n : Nat} (h : n < 64) : decodeChar (encodeSextet n) = some n :=
  sextet_roundTrip n (List.mem_range.mpr h)

/--
`decode` at a two-character list, as a rewrite rule. Two characters are the shortest thing this
codec accepts after the empty string and they carry one byte; there being no padding here, only
their length says they are final.

The left is `decode [x, y]` and the right is that arm of the definition: both characters decoded and
the pair handed to `oneByte`, which returns a byte only when the four spare bits of the second
sextet are zero. `rfl` closes it, so this is the definition restated rather than a claim about it.
-/
private theorem decode_2 (x y : Char) : decode [x, y] =
    match decodeChar x, decodeChar y with
    | some s0, some s1 => oneByte s0 s1
    | _, _ => none := rfl

/--
`decode` at a three-character list, as a rewrite rule. Three characters carry two bytes with two
bits over, the other partial group this codec has.

The left is `decode [x, y, z]` and the right is its arm: three characters decoded and the sextets
handed to `twoBytes`, which requires the last sextet's low two bits to be zero. `rfl` closes it, so
nothing is assumed beyond the definition.
-/
private theorem decode_3 (x y z : Char) : decode [x, y, z] =
    match decodeChar x, decodeChar y, decodeChar z with
    | some s0, some s1, some s2 => twoBytes s0 s1 s2
    | _, _, _ => none := rfl

/--
`decode` at a full group followed by whatever comes after it, as a rewrite rule. This is the
recursive arm, so it is what the induction step of the round trip needs; without padding, a group is
known to be final only by there being nothing after it.

The left is `decode` on four characters followed by an arbitrary `rest`. The right decodes those
four, decodes `rest`, and succeeds only if all five succeed, giving `threeBytes` of the group in
front of the decoded tail. `threeBytes` carries no `Option`: four sextets are exactly three bytes,
with nothing left over to check.
-/
private theorem decode_4 (x y z w : Char) (rest : List Char) :
    decode (x :: y :: z :: w :: rest) =
    match decodeChar x, decodeChar y, decodeChar z, decodeChar w, decode rest with
    | some s0, some s1, some s2, some s3, some tail => some (threeBytes s0 s1 s2 s3 ++ tail)
    | _, _, _, _, _ => none := rfl

/--
A two-character group of in-range sextets decodes to whatever `oneByte` makes of them. Packaging the
two character rewrites into one step keeps the encoder's arithmetic out of the matching, which is
what makes this file elaborate quickly.

`h0` and `h1` bound the sextets below 64 for `sr`, and the conclusion rewrites `decode` of the two
encoded characters to `oneByte s0 s1`, left unevaluated so the caller discharges `s1 % 16 == 0`
where its numbers are known. The sextets are implicit variables, so the rewrite fires on shape
before any arithmetic is unfolded.
-/
private theorem group1 {s0 s1 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) :
    decode [encodeSextet s0, encodeSextet s1] = oneByte s0 s1 := by
  simp only [decode_2, sr h0, sr h1]

/--
A three-character group of in-range sextets decodes to whatever `twoBytes` makes of them; the step
behind the two-byte case of the round trip.

The three hypotheses feed `sr` at each position, and the conclusion gives `twoBytes s0 s1 s2` with
its `s2 % 4 == 0` still to discharge. Stated over sextet variables, it holds of any three in-range
values rather than only those the encoder produces.
-/
private theorem group2 {s0 s1 s2 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64) :
    decode [encodeSextet s0, encodeSextet s1, encodeSextet s2] = twoBytes s0 s1 s2 := by
  simp only [decode_3, sr h0, sr h1, sr h2]

/--
A full group of in-range sextets, in front of a character list known to decode, decodes to its three
bytes in front of that list's bytes. This is the step the induction along a byte list runs on, so it
is the only one here carrying a hypothesis about what follows.

The four bounds feed `sr`, and `hcs : decode cs = some tail` is the round trip already established
for the rest of the input; the conclusion is `some (threeBytes s0 s1 s2 s3 ++ tail)` with no side
condition, since a full group has no spare bits. `cs` and `tail` are implicit, so the lemma applies
at whatever the induction hypothesis is about.
-/
private theorem group3 {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64)
    (h3 : s3 < 64) {cs : List Char} {tail : List UInt8} (hcs : decode cs = some tail) :
    decode (encodeSextet s0 :: encodeSextet s1 :: encodeSextet s2 :: encodeSextet s3 :: cs)
      = some (threeBytes s0 s1 s2 s3 ++ tail) := by
  simp only [decode_4, sr h0, sr h1, sr h2, sr h3, hcs]

/--
A one-byte input round-trips. Base64url spells one byte in two characters with four bits over, and
this is where those bits are shown to be zero rather than assumed.

`encode [a]` is the two-character group; the proof rewrites with `group1` at the encoder's own
sextets, `a.toNat / 4` and `a.toNat % 4 * 16`, each below 64 for any byte. `oneByte` then needs
`a.toNat % 4 * 16 % 16 = 0`, true because that sextet is a multiple of sixteen by construction, and
reassembly is `a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat`. The result is `some [a]`.
-/
private theorem rt1 (a : UInt8) : decode (encode [a]) = some [a] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  simp only [encode]
  rw [group1 (by omega : a.toNat / 4 < 64) (by omega : a.toNat % 4 * 16 < 64), oneByte,
    show a.toNat % 4 * 16 % 16 = 0 by omega,
    show a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat by omega, UInt8.ofNat_toNat]
  rfl

/--
A two-byte input round-trips. Two bytes are spelled in three characters with two bits over; with
`rt1` this covers both lengths that are not a whole group.

`encode [a, b]` reads the pair as `a.toNat * 256 + b.toNat` and cuts three sextets from it; `group2`
is applied at those three with `omega` bounds. `twoBytes` needs the last sextet to be a multiple of
four, which it is by construction, and the two `show` equations recover `a.toNat` and `b.toNat`, the
second straddling two sextets. The result is `some [a, b]`.
-/
private theorem rt2 (a b : UInt8) : decode (encode [a, b]) = some [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  simp only [encode]
  rw [group2 (by omega : (a.toNat * 256 + b.toNat) / 1024 < 64)
      (by omega : (a.toNat * 256 + b.toNat) / 16 % 64 < 64)
      (by omega : (a.toNat * 256 + b.toNat) % 16 * 4 < 64),
    twoBytes,
    show (a.toNat * 256 + b.toNat) % 16 * 4 % 4 = 0 by omega,
    show (a.toNat * 256 + b.toNat) / 1024 * 4 + (a.toNat * 256 + b.toNat) / 16 % 64 / 16
      = a.toNat by omega,
    show (a.toNat * 256 + b.toNat) / 16 % 64 % 16 * 16 + (a.toNat * 256 + b.toNat) % 16 * 4 / 4
      = b.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

/--
The inductive step: three more bytes in front of a list that already round-trips still round-trips.
Three bytes are a whole group with nothing left over, which is why the encoding of a long input is
the concatenation of independent groups.

`ih` is the round trip for `rest`, and `encode` on `a :: b :: c :: rest` is four characters followed
by `encode rest`, so `group3` applies with `ih` as its hypothesis about the tail. The four bounds
are `omega` facts about the sextets cut from the twenty-four-bit number the three bytes make, three
`show` equations reassemble the bytes, and no spare-bit condition arises. The result is
`some (a :: b :: c :: rest)`.
-/
private theorem rt3 (a b c : UInt8) (rest : List UInt8)
    (ih : decode (encode rest) = some rest) :
    decode (encode (a :: b :: c :: rest)) = some (a :: b :: c :: rest) := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  simp only [encode]
  rw [group3 (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 < 64) ih,
    threeBytes,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 * 4
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 / 16 = a.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 % 16 * 16
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 / 4 = b.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 % 4 * 64
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 = c.toNat by omega]
  simp only [UInt8.ofNat_toNat, List.cons_append, List.nil_append]

/--
Base64url encoding loses nothing: every byte string is recovered from its own encoding. A value
written into a URL or a token and read back is the value that was written, for every input rather
than for the lengths a vector suite happens to contain.

`encode bytes` is the character list, `decode` returns `Option (List UInt8)`, and `some bytes` says
decoding succeeds and hands back the input unchanged, for every `bytes` including the empty list.
The induction is over `encode.induct`, so the cases are the encoder's own: the one-byte and two-byte
groups and the recursive full group, discharged by `rt1`, `rt2` and `rt3`. Character lists the
encoder never produces are outside the claim, so this does not say that `decode` is injective.
-/
theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => exact rt1 a
  | case3 a b => exact rt2 a b
  | case4 a b c rest ih => exact rt3 a b c rest ih

/--
A character the decoder accepts is the one the encoder would have written for the sextet it answers
with. This is what makes the alphabet an injection rather than a lookup table, and every rejection
the canonicity theorem below accounts for rests on it.

`decodeChar c = some n` says searching `alphabet` for `c` found it at position `n`. The conclusion
is that `n` is a sextet value, below 64, and that `encodeSextet n`, the character sitting at
position `n`, is `c` again. `findIdx?` answering `some n` supplies both halves: the index is within
the list and the element there matches. Only the alphabet's length is used, not its contents, but
it is proved here rather than borrowed because the two alphabets are different lists.
-/
private theorem decodeChar_sound {c : Char} {n : Nat} (h : decodeChar c = some n) :
    n < 64 ∧ encodeSextet n = c := by
  rw [decodeChar, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hn, hp, -⟩ := h
  exact ⟨hn, by simpa [encodeSextet, List.getElem?_eq_getElem hn] using hp⟩

/--
Every character list the decoder accepts is the encoding of what it hands back. This is the claim a
consumer needs against a rewritten token: a byte string has one spelling, so two different strings
never decode to the same bytes, and a signature over one of them cannot be carried to another. It
also settles each individual rejection at once, because a string carrying `=`, `+` or `/`, a string
of length `4n + 1`, and a string whose final sextet has bits set below the bytes it carries are all
strings `encode` cannot produce.

`decode cs = some bs` is the decoder succeeding on `cs` and answering `bs`, and `encode bs = cs`
says `cs` was that answer's own encoding, character for character. The induction is over
`decode.induct`, so the cases are the decoder's own arms, the ones answering `none` included, where
the hypothesis is contradictory and there is nothing to prove. This is the converse of
`decode_encode` and neither implies the other: that one says nothing is lost, this one says nothing
else is accepted.
-/
theorem encode_decode (cs : List Char) (bs : List UInt8) (h : decode cs = some bs) :
    encode bs = cs := by
  induction cs using decode.induct generalizing bs with
  | case1 => simp [decode] at h; subst h; rfl
  | case2 c => simp [decode] at h
  | case3 x y s0 s1 h1 h0 =>
    obtain ⟨hs0, hx⟩ := decodeChar_sound h0
    obtain ⟨hs1, hy⟩ := decodeChar_sound h1
    simp only [decode_2, h0, h1, oneByte] at h
    split at h
    · rename_i hq
      have hq' : s1 % 16 = 0 := by simpa using hq
      obtain rfl : bs = [UInt8.ofNat (s0 * 4 + s1 / 16)] := (Option.some.inj h).symm
      simp only [encode, toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega)]
      rw [show (s0 * 4 + s1 / 16) / 4 = s0 by omega,
        show (s0 * 4 + s1 / 16) % 4 * 16 = s1 by omega, hx, hy]
    · simp at h
  | case4 x y hno =>
    rw [decode_2] at h
    split at h
    · exact (hno _ _ ‹_› ‹_›).elim
    · simp at h
  | case5 x y z s0 s1 s2 h2 h1 h0 =>
    obtain ⟨hs0, hx⟩ := decodeChar_sound h0
    obtain ⟨hs1, hy⟩ := decodeChar_sound h1
    obtain ⟨hs2, hz⟩ := decodeChar_sound h2
    simp only [decode_3, h0, h1, h2, twoBytes] at h
    split at h
    · rename_i hq
      have hq' : s2 % 4 = 0 := by simpa using hq
      obtain rfl : bs = [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4)] :=
        (Option.some.inj h).symm
      simp only [encode, toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega),
        toNat_ofNat (show s1 % 16 * 16 + s2 / 4 < 256 by omega)]
      rw [show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) / 1024 = s0 by omega,
        show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) / 16 % 64 = s1 by omega,
        show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) % 16 * 4 = s2 by omega,
        hx, hy, hz]
    · simp at h
  | case6 x y z hno =>
    rw [decode_3] at h
    split at h
    · exact (hno _ _ _ ‹_› ‹_› ‹_›).elim
    · simp at h
  | case7 x y z w rest s0 s1 s2 s3 tail hrest h3 h2 h1 h0 ih =>
    obtain ⟨hs0, hx⟩ := decodeChar_sound h0
    obtain ⟨hs1, hy⟩ := decodeChar_sound h1
    obtain ⟨hs2, hz⟩ := decodeChar_sound h2
    obtain ⟨hs3, hw⟩ := decodeChar_sound h3
    rw [decode_4, h0, h1, h2, h3, hrest] at h
    obtain rfl : bs = threeBytes s0 s1 s2 s3 ++ tail := (Option.some.inj h).symm
    simp only [threeBytes, List.cons_append, List.nil_append, encode,
      toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega),
      toNat_ofNat (show s1 % 16 * 16 + s2 / 4 < 256 by omega),
      toNat_ofNat (show s2 % 4 * 64 + s3 < 256 by omega)]
    rw [show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
        / 262144 = s0 by omega,
      show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
        / 4096 % 64 = s1 by omega,
      show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
        / 64 % 64 = s2 by omega,
      show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
        % 64 = s3 by omega,
      hx, hy, hz, hw, ih tail hrest]
  | case8 x y z w rest hno ih =>
    rw [decode_4] at h
    split at h
    · exact (hno _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›).elim
    · simp at h


end Base64Url


namespace Base64
open Leancrypto.Codec.Base64

/--
Every value six bits can take survives being written as a standard base64 character and read back.
The `+` and `/` that end this alphabet are exactly the two characters `Leancrypto.Codec.Base64Url` must not
accept, so each codec establishes this against its own alphabet rather than sharing one proof.

`List.range 64` is `0` through `63`, exactly the sextet values; `encodeSextet n` indexes `alphabet`
and `decodeChar` searches it for an exact match, answering with the index, which the equation says
is `n` again. `decide` covers all sixty-four, so a repeated character in the literal would be caught
here, since a duplicate would send `findIdx?` to the earlier position.
-/
private theorem sextet_roundTrip : ∀ n ∈ List.range 64, decodeChar (encodeSextet n) = some n := by
  decide

/--
The character round trip in the form the group lemmas use, taking a bound rather than membership of
a list. As in the other namespaces, the bound is what the use sites already have from `omega`.

`h : n < 64` becomes `n ∈ List.range 64` by `List.mem_range`, and the conclusion is this namespace's
`sextet_roundTrip` at that `n`, so nothing further is claimed. The implicit `n` lets a rewrite fix
it by unification.
-/
private theorem sr {n : Nat} (h : n < 64) : decodeChar (encodeSextet n) = some n :=
  sextet_roundTrip n (List.mem_range.mpr h)

/--
No sextet encodes to the padding character. `decode` tells a padded final group from a full one by
looking for `=`, so were the alphabet to contain one, the meaning of a group would depend on its
contents rather than on its position.

`pad` is `'='`, and the equation says the comparison against it is `false` for each of the
sixty-four in-range sextets. So `encodeSextet` returns `pad` only through the `getD` fallback for an
index the alphabet does not have, which `keep_sextet` deals with separately. `decide` checks all
sixty-four.
-/
private theorem sextet_notPad : ∀ n ∈ List.range 64, (encodeSextet n == pad) = false := by
  decide

/--
The same separation from the padding character, taking a bound rather than membership of a list,
which is the form the group lemmas can use. `group2` and `group3_last` each need to know that a
particular character is not `=`.

`h : n < 64` transports to `n ∈ List.range 64` by `List.mem_range` and the conclusion is
`sextet_notPad`'s body at that `n`; the fact is unchanged, only the shape of its hypothesis.
-/
private theorem np {n : Nat} (h : n < 64) : (encodeSextet n == pad) = false :=
  sextet_notPad n (List.mem_range.mpr h)

/--
`decode` at a four-character list is exactly `finalGroup`. Padding may appear only in the last
group, and this is the arm that admits it, so every proof about a padded input goes through here.

The left is `decode` on exactly four characters with nothing after them; the right is `finalGroup`,
which inspects the last two positions for `=` and dispatches to `oneByte`, `twoBytes` or `fullGroup`
accordingly. `rfl` closes it, so this is the definition's arm restated rather than a claim about it.
-/
private theorem decode_4 (x y z w : Char) : decode [x, y, z, w] = finalGroup x y z w := rfl

/--
`decode` at a group with at least one character after it, as a rewrite rule. Anything but the last
group must be full, and this is where that is enforced.

The left is `decode` on four characters followed by `v :: rest`, a tail written so as to be
non-empty. The right requires `fullGroup` on the four and a successful `decode` of the tail,
concatenating the group's three bytes onto it. `fullGroup` decodes all four characters and
`decodeChar pad` is `none`, so an `=` anywhere but the final group is refused here, without a rule
of its own that could be got round.
-/
private theorem decode_5 (x y z w v : Char) (rest : List Char) :
    decode (x :: y :: z :: w :: v :: rest) =
    match fullGroup x y z w, decode (v :: rest) with
    | some bytes, some tail => some (bytes ++ tail)
    | _, _ => none := rfl

/--
Encoding a non-empty byte list yields a non-empty character list. `decode` chooses between its two
arms by whether four characters are the whole input, so a lemma about a group followed by an encoded
tail has to know that such a tail is either empty or begins with a character.

The statement is `∃ c cs, encode (a :: rest) = c :: cs`, for every leading byte `a` and every
`rest`. The three cases are the three arms of `encode`, each of which produces a literal list of
four characters, or four followed by the encoding of what remains, so each closes by `rfl` on the
witnesses. Nothing depends on the values of the bytes, only on which arm the length selects.
-/
private theorem encode_cons : ∀ (a : UInt8) (rest : List UInt8),
    ∃ c cs, encode (a :: rest) = c :: cs
  | _, [] => ⟨_, _, rfl⟩
  | _, [_] => ⟨_, _, rfl⟩
  | _, _ :: _ :: _ => ⟨_, _, rfl⟩

/--
A final group of two in-range sextets and two pad characters decodes to whatever `oneByte` makes of
them. That is the shape a one-byte input encodes to, so it is the step `rt1` turns on.

`h0` and `h1` bound the sextets below 64 for `sr`. The conclusion hands `finalGroup` the two encoded
characters followed by two `pad`s, which takes the branch where both of the last two positions are
`=` and calls `oneByte s0 s1`, left unevaluated so the caller discharges its `s1 % 16 == 0` at its
own arithmetic.
-/
private theorem group1 {s0 s1 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) :
    decode [encodeSextet s0, encodeSextet s1, pad, pad] = oneByte s0 s1 := by
  simp [decode_4, finalGroup, sr h0, sr h1]

/--
A final group of three in-range sextets and one pad character decodes to whatever `twoBytes` makes
of them. That is the shape a two-byte input encodes to, and so the step `rt2` turns on.

The three bounds feed `sr`, and `np h2` is what rules out the third character being `=` itself,
which would send `finalGroup` down the two-pad branch and mean something else entirely. With that
settled the group takes the one-pad branch and yields `twoBytes s0 s1 s2`, its `s2 % 4 == 0` left
for the caller.
-/
private theorem group2 {s0 s1 s2 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64) :
    decode [encodeSextet s0, encodeSextet s1, encodeSextet s2, pad] = twoBytes s0 s1 s2 := by
  simp [decode_4, finalGroup, np h2, sr h0, sr h1, sr h2]

/--
A full group with nothing after it decodes to its three bytes. `decode` reaches a four-character
input through `finalGroup` rather than `fullGroup`, so this case needs a step of its own even though
no padding is involved.

The four bounds feed `sr`, and `np h3` shows the last character is not `pad`, which is what makes
`finalGroup` fall through to `fullGroup` instead of reading the group as padded. The result is
`some (threeBytes s0 s1 s2 s3)` with no condition attached: four sextets are exactly three bytes, so
there are no spare bits to require anything of.
-/
private theorem group3_last {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64)
    (h3 : s3 < 64) :
    decode [encodeSextet s0, encodeSextet s1, encodeSextet s2, encodeSextet s3]
      = some (threeBytes s0 s1 s2 s3) := by
  simp [decode_4, finalGroup, np h3, fullGroup, sr h0, sr h1, sr h2, sr h3]

/--
A full group in front of another encoding decodes to its three bytes in front of whatever that
encoding decodes to. This is the step that carries the induction along a byte list, and it has to
hold whether or not the group turns out to be the last one.

The four bounds feed `sr` and `ih` is the round trip already established for `bs`. The proof splits
on `bs`: empty, where `encode bs` is `[]`, the four characters are the whole input and `group3_last`
applies; and non-empty, where `encode_cons` supplies a first character so that `decode_5` applies
and `fullGroup` handles the group. Stating the tail as `encode bs` rather than as an arbitrary
character list is what makes that split available.
-/
private theorem group3 {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64)
    (h3 : s3 < 64) {bs : List UInt8} (ih : decode (encode bs) = some bs) :
    decode (encodeSextet s0 :: encodeSextet s1 :: encodeSextet s2 :: encodeSextet s3 :: encode bs)
      = some (threeBytes s0 s1 s2 s3 ++ bs) := by
  match bs with
  | [] => simpa only [encode, List.append_nil] using group3_last h0 h1 h2 h3
  | d :: t =>
    obtain ⟨c, cs, hc⟩ := encode_cons d t
    rw [hc] at ih ⊢
    simp only [decode_5, fullGroup, sr h0, sr h1, sr h2, sr h3, ih]


/--
A one-byte input round-trips. One byte is spelled as two sextets and two pad characters, four bits
over, and this is where those bits are shown to be zero rather than assumed.

`encode [a]` is that padded group; the proof rewrites with `group1` at the encoder's own sextets,
`a.toNat / 4` and `a.toNat % 4 * 16`, each below 64 for any byte. `oneByte` then needs
`a.toNat % 4 * 16 % 16 = 0`, true because that sextet is a multiple of sixteen by construction, and
reassembly is `a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat`. The result is `some [a]`.
-/
private theorem rt1 (a : UInt8) : decode (encode [a]) = some [a] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  simp only [encode]
  rw [group1 (by omega : a.toNat / 4 < 64) (by omega : a.toNat % 4 * 16 < 64), oneByte,
    show a.toNat % 4 * 16 % 16 = 0 by omega,
    show a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat by omega, UInt8.ofNat_toNat]
  rfl

/--
A two-byte input round-trips. Two bytes are spelled as three sextets and one pad character, two bits
over; with `rt1` this covers both of the lengths that need padding at all.

`encode [a, b]` reads the pair as `a.toNat * 256 + b.toNat` and cuts three sextets from it; `group2`
is applied at those three with `omega` bounds, which is all it needs, since it settles internally
that the third character is not padding. `twoBytes` needs the last sextet to be a multiple of four,
and the two `show` equations recover `a.toNat` and `b.toNat`, the second straddling two sextets. The
result is `some [a, b]`.
-/
private theorem rt2 (a b : UInt8) : decode (encode [a, b]) = some [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  simp only [encode]
  rw [group2 (by omega : (a.toNat * 256 + b.toNat) / 1024 < 64)
      (by omega : (a.toNat * 256 + b.toNat) / 16 % 64 < 64)
      (by omega : (a.toNat * 256 + b.toNat) % 16 * 4 < 64),
    twoBytes,
    show (a.toNat * 256 + b.toNat) % 16 * 4 % 4 = 0 by omega,
    show (a.toNat * 256 + b.toNat) / 1024 * 4 + (a.toNat * 256 + b.toNat) / 16 % 64 / 16
      = a.toNat by omega,
    show (a.toNat * 256 + b.toNat) / 16 % 64 % 16 * 16 + (a.toNat * 256 + b.toNat) % 16 * 4 / 4
      = b.toNat by omega]
  simp only [UInt8.ofNat_toNat]
  rfl

/--
The inductive step: three more bytes in front of a list that already round-trips still round-trips.
Three bytes are a whole group, with nothing left over and no padding, which is why the encoding of a
longer input is the concatenation of independent groups.

`ih` is the round trip for `rest`, and `encode` on `a :: b :: c :: rest` is four characters followed
by `encode rest`, so `group3` applies with `ih` as its hypothesis about the tail, covering an empty
and a non-empty `rest` alike. The four bounds are `omega` facts about the sextets cut from the
twenty-four-bit number the bytes make, three `show` equations reassemble them, and no spare-bit
condition arises. The result is `some (a :: b :: c :: rest)`.
-/
private theorem rt3 (a b c : UInt8) (rest : List UInt8)
    (ih : decode (encode rest) = some rest) :
    decode (encode (a :: b :: c :: rest)) = some (a :: b :: c :: rest) := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  simp only [encode]
  rw [group3 (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 < 64)
      (by omega : (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 < 64) ih,
    threeBytes,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 * 4
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 / 16 = a.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 % 16 * 16
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 / 4 = b.toNat by omega,
    show (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 % 4 * 64
      + (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 = c.toNat by omega]
  simp only [UInt8.ofNat_toNat, List.cons_append, List.nil_append]

/--
Base64 encoding loses nothing at the level of character lists: every byte string is recovered from
its own encoding, padding and all. A PEM body written here and read back is the same key, for every
input rather than for the lengths the RFC publishes vectors for.

`encode bytes` is the character list, `decode` returns `Option (List UInt8)`, and `some bytes` says
decoding succeeds and returns the input unchanged, for every `bytes` including the empty list. The
induction is over `encode.induct`, so its cases are the encoder's own: the two padded groups and the
recursive full group, discharged by `rt1`, `rt2` and `rt3`. It says nothing about character lists
the encoder never produces; those are what the refusals in `Tests.Base64Codec` are about.
-/
theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => exact rt1 a
  | case3 a b => exact rt2 a b
  | case4 a b c rest ih => exact rt3 a b c rest ih

/--
No alphabet character is dropped by the filter `decodeString` applies. That filter runs before
decoding, so a character it removed would silently change the value decoded rather than cause a
failure.

`keep c` is `c != '\n' && c != '\r'`, and the equation says it answers `true` for each of the
sixty-four in-range sextets, so nothing the encoder takes from the alphabet is removed. `decide`
checks all sixty-four, which is every value a sextet can take.
-/
private theorem keep_range : ∀ n ∈ List.range 64, keep (encodeSextet n) = true := by decide

/--
The padding character survives the filter too. Padding is what tells `finalGroup` how many bytes the
last group carries, so removing it would turn a well-formed short group into a malformed input.

`pad` is `'='`, which is neither of the two characters `keep` rejects, so the equation holds by
evaluation and `decide` performs it. It is a statement about the character alone, so it applies
wherever `pad` occurs, not only at the end of an encoding.
-/
private theorem keep_pad : keep pad = true := by decide

/--
The alphabet holds exactly sixty-four characters. `encodeSextet` falls back to `pad` for an index
the alphabet does not have, so where that boundary lies is what lets `keep_sextet` cover the indices
`keep_range` does not.

`alphabet` is the RFC 4648 §4 alphabet written as a string literal and taken to a list of
characters, and `64` is the number of values six bits index. `rfl` evaluates the literal, so this
checks the literal as written rather than the intention behind it; a miscount in either direction
shows up here rather than as a decoding failure later.
-/
private theorem alphabet_length : alphabet.length = 64 := rfl

/--
The filter keeps whatever `encodeSextet` returns, for any natural number, in range or not.
`filter_encode` has to reason about the encoder's output without carrying a bound on every sextet
expression in it, and this removes the need for one.

The argument is an unrestricted `Nat`, so nothing about it is assumed. The proof splits at 64: below
that `keep_range` applies, and at or above it `alphabet_length` puts the index past the end of the
alphabet, so `getD` returns `pad` and `keep_pad` applies. The statement is therefore a claim about
every index rather than a bound quietly assumed, which is why no use of it carries a side condition.
-/
private theorem keep_sextet (n : Nat) : keep (encodeSextet n) = true := by
  rcases Nat.lt_or_ge n 64 with h | h
  · exact keep_range n (List.mem_range.mpr h)
  · have hlen : alphabet.length ≤ n := by rw [alphabet_length]; omega
    rw [show encodeSextet n = pad by simp [encodeSextet, List.getElem?_eq_none hlen]]
    exact keep_pad

/--
Filtering line endings out of an encoding leaves it unchanged. `decodeString` filters whatever
string it is given, so this is what makes that filter invisible to a value which was never wrapped.

`encode bytes` is the character list and `.filter keep` removes `\n` and `\r`; the equation says
nothing is removed, for every input including the empty list, where both sides are `[]`. The
induction is over `encode.induct` and each case is closed by `keep_sextet` and `keep_pad`, so padded
and unpadded groups are covered alike.
-/
private theorem filter_encode (bytes : List UInt8) : (encode bytes).filter keep = encode bytes := by
  induction bytes using encode.induct with
  | case1 => rfl
  | case2 a => simp [encode, keep_sextet, keep_pad]
  | case3 a b => simp [encode, keep_sextet, keep_pad]
  | case4 a b c rest ih => simp [encode, keep_sextet, ih]

/--
The round trip at the level the rest of the library actually calls: `ByteArray` in, `String` out,
and the same `ByteArray` back. `decode_encode` is about lists of characters and bytes, and it is
between those and the string and array wrappers that a filter or a conversion could still lose
something.

`encodeString` encodes the array's bytes and packs the characters into a `String`; `decodeString`
takes that string back to a character list, filters it with `keep`, decodes, and repacks into a
`ByteArray`. The equation says the result is `some bytes`, the array it started from.
`filter_encode` disposes of the filtering step and `decode_encode` of the decoding, so what remains
is that `String.ofList` and `String.toList` are inverse, which is `String.toList_ofList` from core
rather than anything established here.
-/
theorem decodeString_encodeString (bytes : ByteArray) :
    decodeString (encodeString bytes) = some bytes := by
  simp [decodeString, encodeString, String.toList_ofList, filter_encode, decode_encode]
/--
A character the decoder accepts is the one the encoder would have written for the sextet it answers
with. The same fact as in the base64url namespace and not the same proof, because the two alphabets
disagree in their last two positions and this one has to be about this list.

`decodeChar c = some n` says searching `alphabet` for `c` found it at position `n`. The conclusion
is that `n` is a sextet value, below 64, and that `encodeSextet n` is `c` again. `findIdx?`
answering `some n` gives both: the index is within the list and the element there matches. `pad` is
not in the alphabet, so no `n` at all answers for `=`, which is what keeps padding out of the
positions where the encoder never writes it.
-/
private theorem decodeChar_sound {c : Char} {n : Nat} (h : decodeChar c = some n) :
    n < 64 ∧ encodeSextet n = c := by
  rw [decodeChar, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hn, hp, -⟩ := h
  exact ⟨hn, by simpa [encodeSextet, List.getElem?_eq_getElem hn] using hp⟩

/--
The three bytes of a full group, in front of anything at all, encode back to the four characters
its sextets name. A full group is reached by two different arms of the decoder, the four-character
input and the recursive one, so the step is stated once over an arbitrary tail rather than twice.

The four bounds are what `encodeSextet` needs in order to invert `decodeChar`. `threeBytes` packs
the sextets into three bytes and the conclusion cuts the same four sextets back out of them, leaving
`encode tail` where it was. Each byte is below 256, so `toNat_ofNat` applies, and the twenty-four
bit number the three bytes make divides back into exactly the sextets it was built from.
-/
private theorem encode_threeBytes {s0 s1 s2 s3 : Nat} (h0 : s0 < 64) (h1 : s1 < 64) (h2 : s2 < 64)
    (h3 : s3 < 64) (tail : List UInt8) :
    encode (threeBytes s0 s1 s2 s3 ++ tail)
      = encodeSextet s0 :: encodeSextet s1 :: encodeSextet s2 :: encodeSextet s3
        :: encode tail := by
  simp only [threeBytes, List.cons_append, List.nil_append, encode,
    toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega),
    toNat_ofNat (show s1 % 16 * 16 + s2 / 4 < 256 by omega),
    toNat_ofNat (show s2 % 4 * 64 + s3 < 256 by omega)]
  rw [show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
      / 262144 = s0 by omega,
    show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
      / 4096 % 64 = s1 by omega,
    show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
      / 64 % 64 = s2 by omega,
    show ((s0 * 4 + s1 / 16) * 65536 + (s1 % 16 * 16 + s2 / 4) * 256 + (s2 % 4 * 64 + s3))
      % 64 = s3 by omega]

/--
Every character list the decoder accepts is the encoding of what it hands back. The claim matters
more here than for base64url because padding gives a permissive decoder more room: `=` in the wrong
place, a padded group that is not the last, or padding longer than the final group is short would
each give a byte string a second spelling. None of them is `encode` of anything, so none of them is
accepted.

`decode cs = some bs` is the decoder succeeding on `cs` and answering `bs`, and `encode bs = cs`
says `cs` was that answer's own encoding. The induction is over `decode.induct`, whose cases are the
decoder's arms: the empty input, the four characters that are the whole input, a full group with
something after it, and the lengths that are not a multiple of four, where the hypothesis is
contradictory. The `=` cases are reached through `finalGroup`, and the trailing sextet's spare bits
are pinned by `oneByte` and `twoBytes` on the way through.
-/
theorem encode_decode (cs : List Char) (bs : List UInt8) (h : decode cs = some bs) :
    encode bs = cs := by
  induction cs using decode.induct generalizing bs with
  | case1 => simp [decode] at h; subst h; rfl
  | case2 x y z w =>
    simp only [decode_4, finalGroup] at h
    split at h
    · rename_i hw
      obtain rfl : w = pad := by simpa using hw
      split at h
      · rename_i hz
        obtain rfl : z = pad := by simpa using hz
        split at h
        · rename_i s0 s1 h0 h1
          obtain ⟨hs0, hx⟩ := decodeChar_sound h0
          obtain ⟨hs1, hy⟩ := decodeChar_sound h1
          simp only [oneByte] at h
          split at h
          · rename_i hq
            have hq' : s1 % 16 = 0 := by simpa using hq
            obtain rfl : bs = [UInt8.ofNat (s0 * 4 + s1 / 16)] := (Option.some.inj h).symm
            simp only [encode, toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega)]
            rw [show (s0 * 4 + s1 / 16) / 4 = s0 by omega,
              show (s0 * 4 + s1 / 16) % 4 * 16 = s1 by omega, hx, hy]
          · simp at h
        · simp at h
      · split at h
        · rename_i s0 s1 s2 h0 h1 h2
          obtain ⟨hs0, hx⟩ := decodeChar_sound h0
          obtain ⟨hs1, hy⟩ := decodeChar_sound h1
          obtain ⟨hs2, hz⟩ := decodeChar_sound h2
          simp only [twoBytes] at h
          split at h
          · rename_i hq
            have hq' : s2 % 4 = 0 := by simpa using hq
            obtain rfl :
                bs = [UInt8.ofNat (s0 * 4 + s1 / 16), UInt8.ofNat (s1 % 16 * 16 + s2 / 4)] :=
              (Option.some.inj h).symm
            simp only [encode, toNat_ofNat (show s0 * 4 + s1 / 16 < 256 by omega),
              toNat_ofNat (show s1 % 16 * 16 + s2 / 4 < 256 by omega)]
            rw [show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) / 1024 = s0 by omega,
              show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) / 16 % 64 = s1 by omega,
              show ((s0 * 4 + s1 / 16) * 256 + (s1 % 16 * 16 + s2 / 4)) % 16 * 4 = s2 by omega,
              hx, hy, hz]
          · simp at h
        · simp at h
    · simp only [fullGroup] at h
      split at h
      · rename_i s0 s1 s2 s3 h0 h1 h2 h3
        obtain ⟨hs0, hx⟩ := decodeChar_sound h0
        obtain ⟨hs1, hy⟩ := decodeChar_sound h1
        obtain ⟨hs2, hz⟩ := decodeChar_sound h2
        obtain ⟨hs3, hw⟩ := decodeChar_sound h3
        obtain rfl : bs = threeBytes s0 s1 s2 s3 := (Option.some.inj h).symm
        rw [show threeBytes s0 s1 s2 s3 = threeBytes s0 s1 s2 s3 ++ []
            from (List.append_nil _).symm,
          encode_threeBytes hs0 hs1 hs2 hs3, hx, hy, hz, hw]
        rfl
      · simp at h
  | case3 x y z w rest hne bytes tail hrest hfull ih =>
    obtain ⟨v, rest', rfl⟩ : ∃ v rest', rest = v :: rest' := by
      cases rest with
      | nil => exact absurd rfl hne
      | cons v r => exact ⟨v, r, rfl⟩
    rw [decode_5, hfull, hrest] at h
    obtain rfl : bs = bytes ++ tail := (Option.some.inj h).symm
    simp only [fullGroup] at hfull
    split at hfull
    · rename_i s0 s1 s2 s3 h0 h1 h2 h3
      obtain ⟨hs0, hx⟩ := decodeChar_sound h0
      obtain ⟨hs1, hy⟩ := decodeChar_sound h1
      obtain ⟨hs2, hz⟩ := decodeChar_sound h2
      obtain ⟨hs3, hw⟩ := decodeChar_sound h3
      obtain rfl : bytes = threeBytes s0 s1 s2 s3 := (Option.some.inj hfull).symm
      rw [encode_threeBytes hs0 hs1 hs2 hs3, hx, hy, hz, hw, ih tail hrest]
    · simp at hfull
  | case4 x y z w rest hne hno ih =>
    obtain ⟨v, rest', rfl⟩ : ∃ v rest', rest = v :: rest' := by
      cases rest with
      | nil => exact absurd rfl hne
      | cons v r => exact ⟨v, r, rfl⟩
    rw [decode_5] at h
    split at h
    · exact (hno _ _ ‹_› ‹_›).elim
    · simp at h
  | case5 t hne h4 h5 =>
    exfalso
    cases t with
    | nil => exact hne rfl
    | cons a t1 =>
      cases t1 with
      | nil => simp [decode] at h
      | cons b t2 =>
        cases t2 with
        | nil => simp [decode] at h
        | cons c t3 =>
          cases t3 with
          | nil => simp [decode] at h
          | cons d t4 => exact h5 a b c d t4 rfl


end Base64

end Tests.Encodings
