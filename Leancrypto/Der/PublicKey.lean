/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Leancrypto.Codec.Base64
public import Leancrypto.Rsa
import Leancrypto.Der.Reader
import Leancrypto.Der.Writer

/-!
Reading an RSA public key out of a `SubjectPublicKeyInfo`, an X.509 certificate, or the PEM text a
certificate arrives in over HTTP, and writing a `SubjectPublicKeyInfo` back for an RSA or an
elliptic curve key.

This reads a key. It does not validate the certificate: not the chain, not the signature on it,
not the validity dates, not the revocation status, not the subject, not the issuer. A key returned
here is the key that certificate carries, and nothing has been said about whether that certificate
should be believed.

A caller is therefore obliged to establish that separately, and the usual way is the transport: to
fetch the certificate over HTTPS from a host it has checked against an allowlist it controls, so
that TLS validates the chain on its behalf. A caller that fetches over plain HTTP, or that fetches
from whatever URL the payload it is about to verify happened to name, has built a verifier that
confirms the attacker signed the attacker's message.
-/

public section

namespace Leancrypto.Der

/-- `1.2.840.113549.1.1.1`, the contents of the `rsaEncryption` identifier, without its tag and
length. -/
def rsaEncryptionOid : ByteArray :=
  ⟨#[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]⟩

/-- The key in the `SubjectPublicKeyInfo` beginning at `index`, and where that structure ends.

Every part is required to be consumed: an algorithm identifier with something after its
parameters, or a bit string with something after the key, is a structure this does not understand
and so is not one it will read a key out of. -/
def publicKeyAt (der : ByteArray) (limit index : Nat) :
    Option (Rsa.PublicKey × Nat) := do
  let info ← readTagged sequenceTag der limit index
  let algorithm ← readTagged sequenceTag der info.next info.start
  let afterOid ← readObjectIdentifier rsaEncryptionOid der algorithm.next algorithm.start
  let afterParameters ← readNull der algorithm.next afterOid
  guard (afterParameters = algorithm.next)
  let (keyStart, keyEnd) ← readBitString der info.next algorithm.next
  guard (keyEnd = info.next)
  let key ← readTagged sequenceTag der keyEnd keyStart
  guard (key.next = keyEnd)
  let (modulus, afterModulus) ← readNat der key.next key.start
  let (exponent, afterExponent) ← readNat der key.next afterModulus
  guard (afterExponent = key.next)
  guard (modulus ≠ 0)
  guard (exponent ≠ 0)
  some ({ modulus, exponent }, info.next)

def publicKeyOfSpki (der : ByteArray) : Option Rsa.PublicKey := do
  let (key, next) ← publicKeyAt der der.size 0
  guard (next = der.size)
  some key

/-- The key from an X.509 certificate. The fields before the key are passed over rather than
interpreted, because none of them says anything this library is in a position to act on. -/
def publicKeyOfCertificate (der : ByteArray) : Option Rsa.PublicKey := do
  let certificate ← readTagged sequenceTag der der.size 0
  guard (certificate.next = der.size)
  let tbs ← readTagged sequenceTag der certificate.next certificate.start
  let first ← readTlv der tbs.next tbs.start
  -- The version is `[0] EXPLICIT` and defaults to v1, so a certificate that omits it begins at
  -- its serial number.
  let serial := if first.tag = contextZeroTag then first.next else tbs.start
  let afterSerial ← skipValue der tbs.next serial
  let afterSignature ← skipValue der tbs.next afterSerial
  let afterIssuer ← skipValue der tbs.next afterSignature
  let afterValidity ← skipValue der tbs.next afterIssuer
  let afterSubject ← skipValue der tbs.next afterValidity
  let (key, _) ← publicKeyAt der tbs.next afterSubject
  some key

/-- The key from the PEM text of a certificate, armour and line breaks and all. Exactly one
`CERTIFICATE` block is accepted: a file holding a chain names several keys, and which of them a
caller meant is not this function's to guess. -/
def publicKeyOfPem (pem : String) : Option Rsa.PublicKey :=
  match pem.splitOn "-----BEGIN CERTIFICATE-----" with
  | [_, afterBegin] =>
    match afterBegin.splitOn "-----END CERTIFICATE-----" with
    | [body, _] => (Leancrypto.Codec.Base64.decodeString body).bind publicKeyOfCertificate
    | _ => none
  | _ => none

/-- `1.2.840.10045.2.1`, the contents of the `id-ecPublicKey` identifier, without its tag and
length. -/
def idEcPublicKeyOid : ByteArray :=
  ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]⟩

/-- `1.2.840.10045.3.1.7`, `prime256v1`, which JOSE names `P-256`. -/
def prime256v1Oid : ByteArray :=
  ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩

/-- `1.3.132.0.34`, `secp384r1`, which JOSE names `P-384`. -/
def secp384r1Oid : ByteArray := ⟨#[0x2b, 0x81, 0x04, 0x00, 0x22]⟩

/-- `1.3.132.0.35`, `secp521r1`, which JOSE names `P-521`. -/
def secp521r1Oid : ByteArray := ⟨#[0x2b, 0x81, 0x04, 0x00, 0x23]⟩

/-- The `SubjectPublicKeyInfo` for an RSA key: the structure `publicKeyOfSpki` reads, written from
the same two numbers it returns. -/
def rsaPublicKeyInfo (key : Rsa.PublicKey) : ByteArray :=
  sequence (sequence (objectIdentifier rsaEncryptionOid ++ null)
    ++ bitString (sequence (integer key.modulus ++ integer key.exponent)))

/-- The `SubjectPublicKeyInfo` for an elliptic curve key, under one of the named curve identifiers
above.

The point goes in as it is handed over. That it is an uncompressed `0x04 || X || Y` of the right
width for the curve, and that it is on that curve at all, are the caller's to establish: nothing
here does curve arithmetic, and nothing here reads this structure back. -/
def ecPublicKeyInfo (curve point : ByteArray) : ByteArray :=
  sequence (sequence (objectIdentifier idEcPublicKeyOid ++ objectIdentifier curve)
    ++ bitString point)

end Leancrypto.Der
