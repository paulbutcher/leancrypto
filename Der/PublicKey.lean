/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Codec.Base64
public import Crypto.Rsa
import Der.Reader

/-!
Reading an RSA public key out of a `SubjectPublicKeyInfo`, an X.509 certificate, or the PEM text a
certificate arrives in over HTTP.

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

namespace Der

/-- `1.2.840.113549.1.1.1`, the contents of the `rsaEncryption` identifier, without its tag and
length. -/
def rsaEncryptionOid : ByteArray :=
  ⟨#[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]⟩

/-- The key in the `SubjectPublicKeyInfo` beginning at `index`, and where that structure ends.

Every part is required to be consumed: an algorithm identifier with something after its
parameters, or a bit string with something after the key, is a structure this does not understand
and so is not one it will read a key out of. -/
def publicKeyAt (der : ByteArray) (limit index : Nat) :
    Option (Crypto.Rsa.PublicKey × Nat) := do
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

def publicKeyOfSpki (der : ByteArray) : Option Crypto.Rsa.PublicKey := do
  let (key, next) ← publicKeyAt der der.size 0
  guard (next = der.size)
  some key

/-- The key from an X.509 certificate. The fields before the key are passed over rather than
interpreted, because none of them says anything this library is in a position to act on. -/
def publicKeyOfCertificate (der : ByteArray) : Option Crypto.Rsa.PublicKey := do
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
def publicKeyOfPem (pem : String) : Option Crypto.Rsa.PublicKey :=
  match pem.splitOn "-----BEGIN CERTIFICATE-----" with
  | [_, afterBegin] =>
    match afterBegin.splitOn "-----END CERTIFICATE-----" with
    | [body, _] => (Codec.Base64.decodeString body).bind publicKeyOfCertificate
    | _ => none
  | _ => none

end Der
