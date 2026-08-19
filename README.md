# leancrypto

SHA-256, HMAC-SHA256, RSA signature verification

| Library | Holds |
| --- | --- |
| `Crypto` | SHA-256 (FIPS 180-4), HMAC-SHA256 (RFC 2104), RSA signature verification (RFC 8017), and a byte comparison with no early exit. |
| `Codec` | Lowercase hex, base64 (RFC 4648 §4), base64url (RFC 4648 §5, unpadded), and Crockford base32. |
| `Der` | As much of DER as reading an RSA public key out of an X.509 certificate needs. |

`Codec` and `Crypto` do not depend on each other. `Der` depends on both, because the structure it
reads is armoured in base64 and the thing it returns is an RSA key. Nothing depends on anything
outside Lean core.

```lean
import Crypto
import Codec
import Der

open Crypto

example : String := Codec.Hex.encodeString (Sha256.hashUtf8 "abc")

example (key : ByteArray) : ByteArray := hmac key "message".toUTF8

example (mac candidate : ByteArray) : Bool := bytesEqual mac candidate

example (pem : String) (message signature : ByteArray) : Bool :=
  match Der.publicKeyOfPem pem with
  | none => false
  | some key => Rsa.verifyPkcs1v15Sha256 key message signature
```

## What signature verification does not do

`Der.publicKeyOfPem` does the bare minimum necessary to read a key. It does not validate
the certificate.

## What is verified

Proved as theorems, for all inputs, in `test`:

- `decode (encode bytes) = some bytes` for hex, base64, base64url and Crockford base32, and
  `decodeString (encodeString bytes) = some bytes` for base64.
- `powMod base exponent modulus = base ^ exponent % modulus`.
- A number renders to exactly the requested width, and reads back as itself below that width.
- Hex output is exactly twice the input length, and contains only lowercase digits.
- `bytesEqual a b = true ↔ a = b`.

Checked against published vectors, not proved:

- That SHA-256 and HMAC-SHA256 agree with the standards (FIPS 180-4, RFC 4231).
- That verification agrees with NIST CAVP `SigVer15`, on its failing cases as well as its passing
  ones (RFC 4648 §10 for base64, checked by reduction rather than at runtime).

Checked against constructed inputs:

- That a signature is refused when it was made over a different message, under a different key, at
  the wrong length, with a padding byte that is not `0xFF`, or with the padding shortened and the
  `DigestInfo` shifted, which is the Bleichenbacher forgery.
- That the DER reader returns no key for a real certificate that has been truncated, extended, or
  altered in one byte of its structure.

Not established either way:

- That `bytesEqual` has no early exit. The code is written to avoid one, but that is a claim about
  how it executes, not about the value it returns. Nothing in signature verification needs it:
  every input there is public.
- How the decoders behave on input the encoders never produce.

## Building

```
lake build
lake test
```
