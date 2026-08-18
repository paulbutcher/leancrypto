# leancrypto

SHA-256, HMAC-SHA256

| Library | Holds |
| --- | --- |
| `Crypto` | SHA-256 (FIPS 180-4), HMAC-SHA256 (RFC 2104), and a byte comparison with no early exit. |
| `Codec` | Lowercase hex, base64url (RFC 4648 §5, unpadded), and Crockford base32. |

Neither depends on the other, and neither depends on anything outside Lean core.

```lean
import Crypto
import Codec

open Crypto

example : String := Codec.Hex.encodeString (Sha256.hashUtf8 "abc")

example (key : ByteArray) : ByteArray := hmac key "message".toUTF8

example (mac candidate : ByteArray) : Bool := bytesEqual mac candidate
```

## What is verified

Proved as theorems, for all inputs, in `test`:

- `decode (encode bytes) = some bytes` for hex, base64url and Crockford base32.
- Hex output is exactly twice the input length, and contains only lowercase digits.
- `bytesEqual a b = true ↔ a = b`.

Checked only against published vectors (FIPS 180-4, RFC 4231), not proved:

- That SHA-256 and HMAC-SHA256 agree with the standards.

Not established either way:

- That `bytesEqual` has no early exit. The code is written to avoid one, but that is a claim about
  how it executes, not about the value it returns.
- How the decoders behave on input the encoders never produce.

## Building

```
lake build
lake test
```
