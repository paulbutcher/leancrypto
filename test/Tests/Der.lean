/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Codec.Base64
import Codec.Hex
import Der

/-!
The reader against a real certificate, and against copies of it that have been damaged.

The fixture is ISRG Root X1, the Let's Encrypt root, whose SHA-256 fingerprint is
`96:BC:EC:06:26:49:76:F3:74:60:77:9A:CF:28:C5:A7:CF:E8:A3:C0:AA:E1:1A:8F:FC:EE:05:C0:BD:DF:08:C6`;
this copy came from the `ca-certificates` trust store. It is here because it is a certificate
somebody else issued, in the form one arrives in, with a 4096-bit key and a version field: the
things a reader tested only against something it generated itself would not meet.

Nothing here says the certificate is trustworthy, and the reader says nothing about that either.

The damaged copies matter more than the intact one. Each is the intact certificate with one thing
changed, and each must produce no key rather than a key: a reader that returned something for any
of them would be a reader whose answer for the intact one meant less than it appears to.
-/

namespace Tests.Der
open Crypto

private def certificateBody : String :=
  "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\n"

private def spkiBody : String :=
  "MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAregkc/QUN/ObnitXKByH\n" ++
  "vty33ziQjG485legePd1wqL+9Wpu9gBPKNveaIZsRJO2sWP9FBJrvx/S6jGbIX7R\n" ++
  "Mzy6SPXded+zuP8S8SGaS8GKhnFpSmZmbI9+PHC/rSkiBvPkwOaAruJLj7eZfpQD\n" ++
  "n9NHl3yZSCNT6DiuTwpvgy7RSVeMgHS22i/QOI17A3AhG3XyMDz6j67d2mOr6xZP\n" ++
  "wo4RS37PC+j/tXcu9LJ7SuBMEiUMcI0DKaDhUyTsE9nuGb8Qs0qMP4mjYVHerIcH\n" ++
  "lPRjcewu4m9bmIHhiVw0eWx27zuQYnnm26SaLybF0BDhDt7ZEI4W+7f3qPfH5QIH\n" ++
  "mI82CJXn4jeWDTZ1nvsOcrEdm7wD+UkF2IHdBbQq1kHprAF2lQoP2N/VvRIfNS8o\n" ++
  "F2zSmMGoCWR3bkc3us6sWV5onX9y1onFBkEpPlk+3Sb1JMkRp1qjTEAfRqGZtac6\n" ++
  "UW6GO559cqcSBXhZ7T5ReBULA4+N0C8Fsj57ShxLcwUS/Mbq4FATfEOTdLPKdOeO\n" ++
  "HwEI0DDUW3E2tAe6wTAwXEi3gjuYpn1giqKjKYLMur2DBBuigwNBodYF8RvCtvCo\n" ++
  "fIY7RqhIKojcdpp2vx9qpT0Zj+s482TeyCsNCij/99viFULUItAnXeF5/hjncIit\n" ++
  "TubZizrG3SdRbv+8ZPUzQ08CAwEAAQ==\n"

private def expectedModulus : String :=
  "ade82473f41437f39b9e2b57281c87bedcb7df38908c6e3ce657a078f775c2a2" ++
  "fef56a6ef6004f28dbde68866c4493b6b163fd14126bbf1fd2ea319b217ed133" ++
  "3cba48f5dd79dfb3b8ff12f1219a4bc18a8671694a66666c8f7e3c70bfad2922" ++
  "06f3e4c0e680aee24b8fb7997e94039fd347977c99482353e838ae4f0a6f832e" ++
  "d149578c8074b6da2fd0388d7b0370211b75f2303cfa8faeddda63abeb164fc2" ++
  "8e114b7ecf0be8ffb5772ef4b27b4ae04c12250c708d0329a0e15324ec13d9ee" ++
  "19bf10b34a8c3f89a36151deac870794f46371ec2ee26f5b9881e1895c34796c" ++
  "76ef3b906279e6dba49a2f26c5d010e10eded9108e16fbb7f7a8f7c7e5020798" ++
  "8f360895e7e237960d36759efb0e72b11d9bbc03f94905d881dd05b42ad641e9" ++
  "ac0176950a0fd8dfd5bd121f352f28176cd298c1a80964776e4737baceac595e" ++
  "689d7f72d689c50641293e593edd26f524c911a75aa34c401f46a199b5a73a51" ++
  "6e863b9e7d72a712057859ed3e5178150b038f8dd02f05b23e7b4a1c4b730512" ++
  "fcc6eae050137c439374b3ca74e78e1f0108d030d45b7136b407bac130305c48" ++
  "b7823b98a67d608aa2a32982ccbabd83041ba2830341a1d605f11bc2b6f0a87c" ++
  "863b46a8482a88dc769a76bf1f6aa53d198feb38f364dec82b0d0a28fff7dbe2" ++
  "1542d422d0275de179fe18e77088ad4ee6d98b3ac6dd27516effbc64f533434f"

private def certificatePem : String :=
  "-----BEGIN CERTIFICATE-----\n" ++ certificateBody ++ "-----END CERTIFICATE-----\n"

private def bytesOf (base64 : String) : ByteArray :=
  (Codec.Base64.decodeString base64).getD ⟨#[]⟩

private def certificateDer : ByteArray := bytesOf certificateBody

private def spkiDer : ByteArray := bytesOf spkiBody

private def expected : Rsa.PublicKey :=
  { modulus := Rsa.natOfBytes ((Codec.Hex.decodeString expectedModulus).getD ⟨#[]⟩),
    exponent := 65537 }

/-- One byte replaced, everything else as issued. -/
private def mutate (der : ByteArray) (index : Nat) (byte : UInt8) : ByteArray :=
  ⟨der.data.setIfInBounds index byte⟩

private def truncate (der : ByteArray) (length : Nat) : ByteArray := der.extract 0 length

def checks : List (String × Bool) :=
  [ ("the key of a real certificate, from its PEM",
      Der.publicKeyOfPem certificatePem == some expected),
    ("the key of a real certificate, from its DER",
      Der.publicKeyOfCertificate certificateDer == some expected),
    ("the key of a real SubjectPublicKeyInfo",
      Der.publicKeyOfSpki spkiDer == some expected),
    -- The armour, and only the armour, tells the PEM reader where the body is.
    ("PEM without the closing armour yields no key",
      Der.publicKeyOfPem ("-----BEGIN CERTIFICATE-----\n" ++ certificateBody) == none),
    ("PEM with no armour at all yields no key",
      Der.publicKeyOfPem certificateBody == none),
    ("PEM holding a chain yields no key rather than a guess",
      Der.publicKeyOfPem (certificatePem ++ certificatePem) == none),
    ("a certificate with a byte appended yields no key",
      Der.publicKeyOfCertificate (certificateDer ++ ⟨#[0x00]⟩) == none),
    ("a certificate truncated by one byte yields no key",
      Der.publicKeyOfCertificate (truncate certificateDer (certificateDer.size - 1)) == none),
    ("a certificate truncated before its key yields no key",
      Der.publicKeyOfCertificate (truncate certificateDer 200) == none),
    ("a certificate truncated to its header yields no key",
      Der.publicKeyOfCertificate (truncate certificateDer 4) == none),
    ("an empty input yields no key",
      Der.publicKeyOfCertificate ⟨#[]⟩ == none),
    -- The offsets below are the fixed part of a SubjectPublicKeyInfo, which is the same shape for
    -- every RSA key: SEQUENCE, then the algorithm SEQUENCE holding a nine-byte OID and NULL, then
    -- the BIT STRING whose first content byte is the count of unused bits.
    ("a SubjectPublicKeyInfo tagged SET rather than SEQUENCE yields no key",
      Der.publicKeyOfSpki (mutate spkiDer 0 0x31) == none),
    ("an algorithm other than rsaEncryption yields no key",
      Der.publicKeyOfSpki (mutate spkiDer 16 0x02) == none),
    ("algorithm parameters other than NULL yield no key",
      Der.publicKeyOfSpki (mutate spkiDer 18 0x01) == none),
    ("a BIT STRING with unused bits yields no key",
      Der.publicKeyOfSpki (mutate spkiDer 23 0x01) == none),
    -- Byte 32 is the leading zero that keeps the modulus positive, and byte 33 the first byte
    -- that needs it.
    ("a negative modulus yields no key",
      Der.publicKeyOfSpki (mutate spkiDer 32 0xff) == none),
    ("a modulus with a leading zero it does not need yields no key",
      Der.publicKeyOfSpki (mutate spkiDer 33 0x00) == none),
    ("a SubjectPublicKeyInfo with a byte appended yields no key",
      Der.publicKeyOfSpki (spkiDer ++ ⟨#[0x00]⟩) == none) ]

/-!
The length forms a DER reader has to refuse, small enough to check by reduction rather than by
running. Each of these is a way to spell something two ways, and a reader that accepts both is a
reader through which one input can be made to mean two things.
-/

theorem reject_indefinite_length : Der.readTlv ⟨#[0x30, 0x80, 0x00, 0x00]⟩ 4 0 = none := by rfl

theorem reject_length_past_end : Der.readTlv ⟨#[0x30, 0x05, 0x00]⟩ 3 0 = none := by rfl

theorem reject_long_form_for_a_short_length :
    Der.readNat ⟨#[0x02, 0x81, 0x01, 0x05]⟩ 4 0 = none := by rfl

theorem reject_length_with_a_leading_zero :
    Der.readNat ⟨#[0x02, 0x82, 0x00, 0x01, 0x05]⟩ 5 0 = none := by rfl

theorem reject_padded_long_form_length :
    Der.readTlv ⟨#[0x30, 0x84, 0x00, 0x00, 0x00, 0x01, 0x05]⟩ 7 0 = none := by rfl

theorem accept_long_form_length : Der.readLength ⟨#[0x81, 0x80]⟩ 2 0 = some (128, 2) := by rfl

theorem reject_negative_integer : Der.readNat ⟨#[0x02, 0x01, 0xff]⟩ 3 0 = none := by rfl

theorem accept_short_integer : Der.readNat ⟨#[0x02, 0x01, 0x05]⟩ 3 0 = some (5, 3) := by rfl

end Tests.Der
