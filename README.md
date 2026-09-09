# leancrypto

Lean4 implementations of SHA-2, HMAC, RSA signature verification, encodings, and a DER reader and writer. No dependencies beyond Lean core.

| Module | Holds |
| --- | --- |
| `Leancrypto.Sha2` | SHA-256, SHA-384 and SHA-512 (FIPS 180-4). |
| `Leancrypto.Hmac` | HMAC over any of the above (RFC 2104). |
| `Leancrypto.Rsa` | RSASSA-PKCS1-v1_5 signature verification (RFC 8017 §8.2.2). |
| `Leancrypto.Rsa.Pss` | RSASSA-PSS signature verification (RFC 8017 §8.1.2). |
| `Leancrypto.Compare` | A byte comparison with no early exit. |
| `Leancrypto.Codec.*` | Lowercase hex, base64 (RFC 4648 §4), base64url (RFC 4648 §5, unpadded), and Crockford base32. |
| `Leancrypto.Der.*` | As much of DER as reading an RSA public key out of an X.509 certificate needs, and writing a `SubjectPublicKeyInfo` back. |

```lean
import Leancrypto

open Leancrypto

example : String := Codec.Hex.encodeString (Sha256.hashUtf8 "abc")

example (key : ByteArray) : ByteArray := hmac .sha384 key "message".toUTF8

example (mac candidate : ByteArray) : Bool := bytesEqual mac candidate

example (pem : String) (message signature : ByteArray) : Bool :=
  match Der.publicKeyOfPem pem with
  | none => false
  | some key => Rsa.verifyPkcs1v15 .sha256 key message signature

example (key : Rsa.PublicKey) (message signature : ByteArray) : Bool :=
  Rsa.Pss.verify .sha256 32 key message signature

example (key : Rsa.PublicKey) : ByteArray := Der.rsaPublicKeyInfo key
```

The salt length passed to `Rsa.Pss.verify` is the one the signature must have been made with. It is not recovered from the signature, because a protocol that pins the length must refuse the others.

## What signature verification does not do

`Der.publicKeyOfPem` does the bare minimum necessary to read a key. It does not validate the certificate.

## What is verified

Proved as theorems, for all inputs, in `test`:

- `decode (encode bytes) = some bytes` for hex, base64, base64url and Crockford base32, and `decodeString (encodeString bytes) = some bytes` for base64.
- The converse for base64 and base64url: `decode cs = some bs → encode bs = cs`, so a byte string has exactly one accepted spelling and nothing the encoder cannot produce is accepted. For hex the same holds with case folded, which is the one liberty that decoder takes.
- `powMod base exponent modulus = base ^ exponent % modulus`.
- A number renders to exactly the requested width, and reads back as itself below that width.
- Hex output is exactly twice the input length, and contains only lowercase digits.
- `bytesEqual a b = true ↔ a = b`.
- The DER writer's digits for a number read back as that number, and carry no leading zero.

Checked against published vectors, not proved:

- That SHA-256, SHA-384 and SHA-512, and HMAC over each of them, agree with the standards (FIPS 180-4, RFC 4231).
- That PKCS#1 v1.5 verification agrees with NIST CAVP `SigVer15` for all three digests, on its failing cases as well as its passing ones.
- That PSS verification agrees with NIST CAVP `SigVerPSS` for all three digests, likewise.
- That base64 agrees with the vectors of RFC 4648 §10, checked by reduction rather than at runtime.

Checked against constructed inputs:

- That a PKCS#1 v1.5 signature is refused when it was made over a different message, under a different key, at the wrong length, with a padding byte that is not `0xFF`, or with the padding shortened and the `DigestInfo` shifted, which is the Bleichenbacher forgery.
- That a PSS block is refused when its trailer is not `0xbc`, when an unused leading bit of the masked `DB` is set, when the `0x01` separator is missing, or when a byte before that separator is not zero. None of the published vectors reaches any of these.
- That each decoder refuses the shapes its encoder cannot produce: padding and the wrong alphabet, characters outside the alphabet, lengths that cannot be an encoding, and trailing bits that are not zero.
- That the DER reader returns no key for a real certificate that has been truncated, extended, or altered in one byte of its structure.
- That a written `SubjectPublicKeyInfo` reads back as the key it was written from, across every modulus width at which the encoding changes shape, and that it is byte for byte the structure OpenSSL writes for the same RSA and P-256 keys.

Not established either way:

- That `bytesEqual` has no early exit. The code is written to avoid one, but that is a claim about how it executes, not about the value it returns. Nothing in signature verification needs it: every input there is public.

## Building

```
lake build
lake test
```
