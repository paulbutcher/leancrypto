# leancrypto

SHA-256, HMAC-SHA256, and the encodings that usually travel with them, for Lean 4.

Two packages needed these and neither should own them: an authentication library digesting
credentials under a server-side pepper, and an AWS SigV4 signer whose signing key is a chain of
HMAC derivations. The alternative to this library is two implementations of SHA-256 in one
dependency graph.

| Library | Holds |
| --- | --- |
| `Crypto` | SHA-256 (FIPS 180-4), HMAC-SHA256 (RFC 2104), and a byte comparison with no early exit. |
| `Codec` | Lowercase hex, base64url (RFC 4648 §5, unpadded), and Crockford base32. |

Neither depends on the other, and neither depends on anything outside Lean core, so a consumer
needing only base64url does not build a hash function.

```lean
import Crypto
import Codec

open Crypto

example : String := Codec.Hex.encodeString (Sha256.hashUtf8 "abc")

example (key : ByteArray) : ByteArray := hmac key "message".toUTF8

example (mac candidate : ByteArray) : Bool := bytesEqual mac candidate
```

Bytes are `ByteArray` throughout. HMAC takes and returns raw bytes rather than an encoding,
because a key derivation chain feeds one result into the next as a key, and an interface returning
hex cannot express that.

## Two things the API insists on

**`Sha256.hashUtf8` says which encoding it hashes.** A hash of a string is a hash of an encoding
of that string, and a caller who does not know which has a bug waiting.

**`bytesEqual` is not called `constantTimeEquals`.** What it offers is the absence of a
data-dependent early exit in its source, which is what stops a byte-by-byte comparison reporting
how long a correct prefix a guess had. It is not constant time: Lean guarantees nothing about the
code it generates, the runtime may short-circuit the `Bool` operations, and nothing here addresses
cache or branch-predictor timing. A threat model needing a real guarantee needs a native
implementation.

## Deliberately absent

No asymmetric anything, no encryption, no other hashes, no key management, no random generation,
and no password hashing. The first two are absent because a library that hashes badly gives a
wrong answer while a library that encrypts badly gives one nobody notices. SHA-512 is a short
piece of work when something needs it; SHA-1 and MD5 should be argued for.

## What this is and is not

A Lean implementation of standard primitives, checked against their published vectors: FIPS 180-4
for SHA-256 and RFC 4231 cases 1, 2, 3, 6 and 7 for HMAC-SHA256, including both oversized-key
cases and the message length at which SHA-256's padding needs an extra block. It has not been
independently reviewed and carries no side-channel claims beyond the one above. A reader whose
threat model needs a reviewed implementation wants a binding to one, not this.

The encodings carry round-trip theorems rather than vectors, and both refuse a non-canonical
encoding: bits beyond the encoded bytes must be zero, so a byte string has exactly one accepted
spelling. Base32 decoding is deliberately more generous than its encoding, folding case, reading
`I` and `L` as `1` and `O` as `0`, and ignoring the hyphens and whitespace a person inserts,
because it exists to be transcribed by hand.

## Building

```
lake build
lake test
```

Warnings are errors. Most of the suite is theorems, which pass by compiling; `lake test` runs the
published vectors, whose value is agreement with a constant no proof could establish.
