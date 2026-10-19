# Changelog

## [0.4.2] - 2026-10-19

* Chore: bump dependencies

## [0.4.1] - 2026-09-10

* `Sha2.size` and `Sha2.blockSize` expose their bodies, so a consumer can reduce them in a proof

## [0.4.0] - 2026-09-09

* Every module and namespace moves under `Leancrypto`, and the three libraries become one
* SHA-384 and SHA-512 alongside SHA-256, with a `Sha2` selector naming one of them
* `hmac` takes that selector as its first argument
* `verifyPkcs1v15Sha256` becomes `Leancrypto.Rsa.verifyPkcs1v15` and takes the same selector
* RSASSA-PSS signature verification
* The decoders are proved to accept nothing their encoders cannot produce
* A DER writer, including `SubjectPublicKeyInfo` for RSA and for elliptic curve keys

## [0.3.1] - 2026-08-29

The documentation has been tightened, and the project now keeps a changelog.

## [0.3.0] - 2026-08-20

Switch to module system

## [0.2.0] - 2026-08-19

* RSA PKCS#1 v1.5 SHA-256 signature verification
* A DER reader that pulls an RSA public key out of an X.509 certificate
* Base64 (RFC 4648 §4) alongside the existing base64url

## [0.1.0] - 2026-08-18

Initial release: SHA-256, HMAC-SHA256, a byte comparison with no early exit, and hex, base64url and Crockford base32 encodings.
