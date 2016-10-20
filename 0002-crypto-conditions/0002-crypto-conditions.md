---
coding: utf-8

title: Crypto-Conditions
docname: draft-thomas-crypto-conditions-01
category: std

pi: [toc, sortrefs, symrefs, comments]
smart_quotes: off

area: security
author:
  -
    ins: S. Thomas
    name: Stefan Thomas
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: stefan@ripple.com
    uri: https://www.ripple.com

  -
    ins: R. Reginelli
    name: Rome Reginelli
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: rome@ripple.com
    uri: https://www.ripple.com

normative:
    RFC3447:
    RFC4648:
    I-D.draft-irtf-cfrg-eddsa-04:
    itu.X680.2015:
        title: "Information technology – Abstract Syntax Notation One (ASN.1): Specification of basic notation"
        target: https://www.itu.int/rec/T-REC-X.680-201508-I/
        author:
            organization: International Telecommunications Union
        date: 2015-08
    itu.X696.2015:
        title: "Information technology – ASN.1 encoding rules: Specification of Octet Encoding Rules (OER)"
        target: http://handle.itu.int/11.1002/1000/12487
        author:
            organization: International Telecommunications Union
        date: 2015-08
        seriesInfo:
            name: "ITU-T"
            value: "Recommendation X.696"

informative:
    RFC2119:
    RFC3110:
    RFC4871:
    LARGE-RSA-EXPONENTS:
        title: Imperial Violet - Very large RSA public exponents (17 Mar 2012)
        target: https://www.imperialviolet.org/2012/03/17/rsados.html
        author:
            fullname: Adam Langley
        date: 2012-03-17
    USING-RSA-EXPONENT-OF-65537:
        title: Cryptography - StackExchange - Impacts of not using RSA exponent of 65537
        target: https://crypto.stackexchange.com/questions/3110/impacts-of-not-using-rsa-exponent-of-65537
        author:
            fullname: http://crypto.stackexchange.com/users/555/fgrieu
        date: 2014-11-18
    KEYLENGTH-RECOMMENDATION:
        title: BlueKrypt - Cryptographic Key Length Recommendation
        target: https://www.keylength.com/en/compare/
        author:
            fullname: Damien Giry
        date: 2015-09-17
    NIST-KEYMANAGEMENT:
        title: NIST - Recommendation for Key Management - Part 1 - General (Revision 3)
        target: http://csrc.nist.gov/publications/nistpubs/800-57/sp800-57_part1_rev3_general.pdf
        date: 2012-07
        author:
            - fullname: Elaine Barker
            - fullname: William Barker
            - fullname: William Burr
            - fullname: William Polk
            - fullname: Miles Smid
    OPENSSL-X509-CERT-EXAMPLES:
        title: OpenSSL - X509 certificate examples for testing and verification
        target: http://fm4dd.com/openssl/certexamples.htm
        author:
            fullname: FM4DD
        date: 2012-07

--- note_Feedback

This specification is a part of the [Interledger Protocol](https://interledger.org/) work. Feedback related to this specification should be sent to <public-interledger@w3.org>.

--- abstract

Crypto-conditions provide a mechanism to describe a signed message such that multiple actors in a distributed system can all verify the same signed message and agree on whether it matches the description. This provides a useful primitive for event-based systems that are distributed on the Internet since we can describe events in a standard deterministic manner (represented by signed messages) and therefore define generic authenticated event handlers.

--- middle

# Introduction
This specification describes a message format for crypto-conditions and fulfillments, with binary and string-based encodings for each.

Crypto-conditions are **distributable event descriptions**. This means crypto-conditions say how to recognize a message without saying exactly what the message is. You can transmit a crypto-condition freely, but you cannot forge the message it describes. For convenience, we hash the description so that the crypto-condition can be a fixed size.

Fulfillments are **cryptographically verifiable messages** that prove an event occurred. If you transmit a fulfillment, then everyone who has the condition can agree that the condition has been met.

In the Interledger protocol, crypto-conditions and fulfillments provide irrepudiable proof that a transfer occurred in one ledger, as messages that can be easily shared with other ledgers. This allows ledgers to escrow funds or hold a transfer conditionally, then execute the transfer automatically when the ledger sees the fulfillment of the stated condition.

Crypto-conditions may also be useful in other contexts where a system needs to make a decision based on predefined criteria, such as smart contracts.

## Terminology
The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC2119][].

Within this specification, the term "condition" refers to the hash of a description of a signed message. The hash function must be preimage-resistant.

The term "fulfillment" refers to a description of a signed message and a signed message that matches the description. We hash the description and compare that to the condition, and also compare the signed message to the description. If the message matches the description and the hash of the description matches the condition, we say that the fulfillment fulfills the condition.

In the simplest case, the fulfillment can be a preimage that hashes to the condition, in which case the preimage is both the description and the message.


## Features
Crypto-conditions are a standard format for expressing conditions and fulfillments. The format supports multiple algorithms, including different hash functions and cryptographic signing schemes. Crypto-conditions can be nested in multiple levels, with each level possibly having multiple signatures.

This format has been designed so that it can be expanded. For example, you can add new cryptographic signature schemes or hash functions. This is important because advances in cryptography frequently render old algorithms insecure or invent newer, more effective algorithms.

The [Bitmask](#bitmask) of a crypto-condition indicates which algorithms it uses, so a compliant implementation can know whether it supports the functionality required to interpret the crypto-condition.

### Multi-Algorithm
The crypto-condition format contains a [Bitmask](#bitmask) that specifies which hash function and signing scheme to use. Any message format for a condition or a fulfillment contains such a bitmask.

Implementations MAY state their supported algorithms by providing a bitmask in the same format. To verify that a given implementation can verify a fulfillment for a given condition, you compare the bitmasks. If all bits set in the condition's bitmask are also set in the implementation's bitmask, then the implementation can verify the condition's fulfillment.

### Multi-Signature
Crypto-conditions can abstract away many of the details of multi-sign. When a party provides a condition, other parties can treat it opaquely and do not need to know about its internal structure. That allows parties to define arbitrary multi-signature setups without breaking compatibility.

Protocol designers can use crypto-conditions as a drop-in replacement for public key signature algorithms and add multi-signature support to their protocols without adding any additional complexity.

### Multi-Level
Crypto-conditions elegantly support weighted multi-signatures and multi-level signatures. A threshold condition has a number of weighted subconditions, and a target threshold. Each subcondition can be a signature or another threshold condition. This provides flexibility in forming complex conditions.

For example, consider a threshold condition that consists of two subconditions, one each from Agnes and Bruce. Agnes's condition can be a signature condition while Bruce's condition is a threshold condition, requiring both Claude and Dan to sign for him.

Weighted signatures allow more complex relationships than simple M-of-N signing. For example, a weighted condition can support an arrangement of subconditions such as, "Either Ron, Adi, and Leonard must approve; or Clifford must approve."



# Format

## Binary Encoding

A description of crypto-conditions is provided in this document using Abstract Syntax Notation One (ASN.1) as defined in [ITU.X680.2015](#itu.X680.2015). Implementations of this spec MUST support encoding and decoding using Octet Encoding Rules (OER) as defined in [ITU.X696.2015](#itu.X696.2015).

## String Types

Crypto-conditions use the following types within string encoding:

BASE10
: Variable-length integer encoded as a base-10 (decimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows.

BASE16
: Variable-length integer encoded as a base-16 (hexadecimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows. No leading zeros.

BASE64URL
: Base64-URL encoding. See [RFC4648](#RFC4648), Section 5.

## Bitmask
Any system that accepts crypto-conditions must be able to state its supported algorithms. It must be possible to verify that all algorithms used in a certain condition are indeed supported even if the fulfillment is not available yet. Therefore, all conditions and fulfillments contain a bitmask to express the required features. Implementations provide a bitmask of features they support.

Each bit represents a different suite of features. Each type of crypto-condition depends on one or more feature suites. If an implementation supports all feature suites that a certain type depends on, the implementation MUST support that condition type. The list of known types and feature suites is the IANA-maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry) .

To save space, the bitmask is encoded as a variable-length integer.

## Condition {#condition-format}
Below are the string and binary encoding formats for a condition.

### String Format {#string-condition-format}

Conditions are ASCII encoded as:

    "cc:" BASE16(type) ":" BASE16(featureBitmask) ":"
        BASE64URL(fingerprint) ":" BASE10(maxFulfillmentLength)


### Binary Format {#binary-condition-format}

Conditions are binary encoded as:

    Condition ::= SEQUENCE {
      type ConditionType,
      featureBitmask OCTET STRING,
      fingerprint OCTET STRING,
      maxFulfillmentLength INTEGER (0..MAX)
    }

    ConditionType ::= INTEGER {
      preimageSha256(0),
      rsaSha256(1),
      prefixSha256(2),
      thresholdSha256(3),
      ed25519(4)
    } (0..65535)

### Fields {#condition-format-fields}

type
: is the numeric type identifier representing the condition type.

featureBitmask
: is an octet string encoding the set of feature suites an implementation must support in order to be able to successfully parse the fulfillment to this condition. This is the boolean OR of the featureBitmask values of the top-level condition type and all subcondition types, recursively.

fingerprint
: is an octet string uniquely representing the condition with respect to other conditions of the same type. Implementations which index conditions MUST use the entire string or binary encoded condition as the key, not just the fingerprint - as different conditions of different types may have the same fingerprint. The length and contents of the fingerprint are defined by the condition type. For most condition types, the fingerprint is a cryptographically secure hash of the data which defines the condition, such as a public key.

maxFulfillmentLength
: is the maximum length of the fulfillment payload that can fulfill this condition, in bytes. The payload size is measured unencoded. (The size of the payload is larger in BASE64URL format.) When a crypto-condition is submitted to an implementation, this implementation MUST verify that it will be able to process a fulfillment with a payload of size maxFulfillmentLength.

### Example Condition

An example condition in string format:

    cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66

The example has the following attributes:

| Field                | Value | Description |
|----------------------|-------|----------------------------------------------|
| preface              | `cc`  | Constant. Indicates this is a condition. |
| type                 | `0`   | Type 0 is [PREIMAGE-SHA-256][]. |
| featuresBitmask      | `3`   | Boolean-OR combination of feature suites SHA-256 (feature bit 0x01) and PREIMAGE (feature bit 0x02). |
| fingerprint          | `dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA` | The hash of the fulfillment for this condition. |
| maxFulfillmentLength | `66`  | The fulfillment payload is 66 bytes long, before being BASE64URL-encoded. |


## Fulfillment {#fulfillment-format}
Below are the string and binary encoding formats for a fulfillment.

### String Format {#string-fulfillment-format}

Fulfillments are ASCII encoded as:

    "cf:" BASE16(type) ":" BASE64URL(payload)

### Binary Format {#binary-fulfillment-format}

Fulfillments are binary encoded as:

    Fulfillment ::= SEQUENCE {
      type ConditionType,
      payload OCTET STRING
    }

### Fields {#fulfillment-format-fields}

type
: is the numeric type identifier representing the condition type. For some condition types the fulfillment will contain further subfulfillments, however the type field always represents the outermost, or top-level, type.

payload
: The payload is an octet string whose internal format is defined by each of the types.

### Example Fulfillment

The following is an example fulfillment in string format, for the [example condition](#example-condition):

    cf:0:VGhlIG9ubHkgYmFzaXMgZm9yIGdvb2QgU29jaWV0eSBpcyB1bmxpbWl0ZWQgY3JlZGl0LuKAlE9zY2FyIFdpbGRl


The example has the following attributes:

| Field                | Value | Description |
|----------------------|-------|----------------------------------------------|
| preface              | `cf`  | Constant. Indicates this is a fulfillment. |
| type                 | `0`   | Type 0 is [PREIMAGE-SHA-256][]. |
| payload              | `VGhlIG...pbGRl` | The BASE64URL-encoded SHA-256 preimage of the condition, since this is a PREIMAGE-SHA-256 type fulfillment. In this case, it is an arbitrary string. |




# Feature Suites {#feature-suites}
This specification defines a starting set of feature suites necessary to support the [Condition Types][] also defined in this specification. Future versions of this spec MAY introduce new feature suites and condition types, which SHALL be registered in the IANA maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry).

Support for a condition type MUST depend on one or more feature suites.  However, all new condition types MUST depend on at least one of the new feature suites. This ensures that all previously created implementations correctly recognize that they do not support the new type.

Feature suites are chosen such that they represent reasonable clusters of functionality. For instance, it is reasonable to require that an implementation which supports SHA-256 in one context MUST support it in all contexts, since it already needed to implement the algorithm.

An implementation which supports a certain set of feature suites MUST accept all condition types which depend only on that set or any subset of feature suites.

| Suite Name | Feature Bit | Feature Bit (BASE16) | Summary |
|------------|-----|------|---------------------------------|
| SHA-256    | 2^0 | 0x01 | The SHA-256 hashing algorithm. |
| PREIMAGE   | 2^1 | 0x02 | The functionality of comparing a hash to a preimage. |
| PREFIX     | 2^2 | 0x04 | The functionality of prefixing the fulfillment with a prefix before generating the condition. |
| THRESHOLD  | 2^3 | 0x08 | The functionality of composing a condition out of several weighted subconditions. |
| RSA-PSS    | 2^4 | 0x10 | The RSA-PSS signature algorithm. |
| ED25519    | 2^5 | 0x20 | The ED25519 signature algorithm. |

## SHA-256 {#sha-256-feature-suite}

The SHA-256 feature suite provides the SHA-256 hash function. SHA-256 is a cryptographic hash function published by the US National Institute of Standards and Technology that produces 256 bits of output. This feature suite is assigned the feature bit 2^0 = 0x01.

## PREIMAGE {#preimage-feature-suite}
The PREIMAGE feature suite provides conditions that use a preimage as a one-time signature. This feature suite is assigned the feature bit 2^1 = 0x02.

The fingerprint of a preimage condition is the hash of an arbitrary value. The payload of a preimage fulfillment is the hashed arbitrary value before hashing, also known as the preimage. Conditions that use this preimage MUST also rely on a cryptographically secure hashing algorithm. Since cryptographically secure hashing functions are preimage-resistant, only the original creator of a preimage condition can produce the preimage, as long as it contains a large amount of random entropy.

## PREFIX {#prefix-feature-suite}
The PREFIX feature suite provides conditions that prepend a fixed message to a subcondition. This feature suite is assigned the feature bit 2^2 = 0x04.

A prefix condition prepends the message to be validated with a constant string before passing it on to the subcondition's validation function. <!-- TODO: better explanation of why -->

## THRESHOLD {#threshold-feature-suite}
The THRESHOLD feature suite provides conditions that have several weighted subconditions and a threshold number. This feature suite is assigned the feature bit 2^3 = 0x08.

Threshold conditions provide flexible multi-signing, such as requiring "M-of-N" subconditions be fulfilled. Subconditions can also be weighted so that one subcondition can count multiple times towards meeting the threshold.

## RSA-PSS {#rsa-pss-feature-suite}
The RSA-PSS feature suite provides the RSS-PSA signature algorithm. RSA-PSS is a signature algorithm based on the RSA cryptosystem, which relates to the problem of factoring the product of two large prime numbers. This feature suite is assigned the feature bit 2^4 = 0x10.

## ED25519 {#ed25519-feature-suite}
The ED25519 feature suite provides the Ed25519 signature algorithm. Ed25519 is a signature algorithm based on the EdDSA signing scheme and the compact elliptic curve known as Ed25519. This feature suite is assigned the feature bit 2^5 = 0x20.




# Condition Types
The following condition types are defined in this version of the specification. Future versions of this spec MAY introduce new feature suites and condition types, which SHALL be registered in the IANA maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry).

## PREIMAGE-SHA-256 {#preimage-sha-256-condition-type}
PREIMAGE-SHA-256 is assigned the type ID 0. It relies on the SHA-256 and PREIMAGE feature suites which corresponds to a feature bitmask of 0x03.

This type of condition is also called a "hashlock". By creating a hash of a difficult-to-guess 256-bit random or pseudo-random integer it is possible to create a condition which the creator can trivially fulfill by publishing the random value. However, for anyone else, the condition is cryptographically hard to fulfill, because they would have to find a preimage for the given condition hash.

Implementations MUST ignore any input message when validating a PREIMAGE-SHA-256 fulfillment.

### Condition {#preimage-sha-256-condition-type-condition}
The fingerprint of a PREIMAGE-SHA-256 condition is the SHA-256 hash of the preimage.

### Fulfillment {#preimage-sha-256-condition-type-fulfillment}
The fulfillment payload of a PREIMAGE-SHA-256 condition is the preimage.

### Example {#preimage-sha-256-example}

Example condition:

    cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66

Example fulfillment:

    cf:0:VGhlIG9ubHkgYmFzaXMgZm9yIGdvb2QgU29jaWV0eSBpcyB1bmxpbWl0ZWQgY3JlZGl0LuKAlE9zY2FyIFdpbGRl


## PREFIX-SHA-256 {#prefix-sha-256-condition-type}
PREFIX-SHA-256 is assigned the type ID 1. It relies on the SHA-256 and PREFIX feature suites which corresponds to a feature bitmask of 0x05.

Prefix conditions provide a way to effective narrow the scope of other conditions. A condition can be used as the fingerprint of a public key to sign an arbitrary message. By creating a prefix subcondition we can narrow the scope from signing an arbitrary message to signing a message with a specific prefix.

When a prefix fulfillment is validated against a message, it will prepend the prefix to the provided message and will use the result as the message to validate against the subfulfillment.

### Condition {#prefix-sha-256-condition-type-condition}
The fingerprint of a PREFIX-SHA-256 condition is the SHA-256 digest of the fingerprint contents given below:

    PrefixSha256FingerprintContents ::= SEQUENCE {
      prefix OCTET STRING,
      condition Condition
    }


prefix
: is an arbitrary octet string which will be prepended to the message during validation.

condition
: is the subcondition which the subfulfillment must match.


### Fulfillment {#prefix-sha-256-condition-type-fulfillment}

    PrefixSha256FulfillmentPayload ::= SEQUENCE {
      prefix OCTET STRING,
      subfulfillment Fulfillment
    }


prefix
: is an arbitrary octet string which will be prepended to the message during validation.

subfulfillment
: is the fulfilled subcondition.

### Example {#prefix-sha-256-example}

Example condition:

    cc:1:25:7myveZs3EaZMMuez-3kq6u69BDNYMYRMi_VF9yIuFLc:102

Example fulfillment:

    cf:1:DUhlbGxvIFdvcmxkISAABGDsFyuTrV5WO_STLHDhJFA0w1Rn7y79TWTr-BloNGfiv7YikfrZQy-PKYucSkiV2-KT9v_aGmja3wzN719HoMchKl_qPNqXo_TAPqny6Kwc7IalHUUhJ6vboJ0bbzMcBwo


## THRESHOLD-SHA-256 {#threshold-sha-256-condition-type}
THRESHOLD-SHA-256 is assigned the type ID 2. It relies on the SHA-256 and THRESHOLD feature suites which corresponds to a feature bitmask of 0x09.

### Condition {#threshold-sha-256-condition-type-condition}
The fingerprint of a THRESHOLD-SHA-256 condition is the SHA-256 digest of the fingerprint contents given below:

    ThresholdSha256FingerprintContents ::= SEQUENCE {
      threshold INTEGER (0..4294967295),
      subconditions SEQUENCE OF ThresholdSubcondition
    }

    ThresholdSubcondition ::= SEQUENCE {
      weight INTEGER (0..4294967295),
      condition Condition
    }

The list of conditions is sorted first based on length, shortest first. Elements of the same length are sorted in lexicographic (big-endian) order, smallest first.  

threshold
: threshold MUST be an integer in the range 1 ... 2^32 - 1. In order to fulfill a threshold condition, the weights of the provided fulfillments MUST be greater than or equal to the threshold.

subconditions
: is the set of subconditions, each provided as a tuple of weight and condition.

weight
: is the numeric weight of this subcondition, i.e. how many times it counts against the threshold.

condition
: is the subcondition.


### Fulfillment {#threshold-sha-256-condition-type-fulfillment}

    ThresholdSha256FulfillmentPayload ::= SEQUENCE {
      threshold INTEGER (0..4294967295),
      subfulfillments SEQUENCE OF ThresholdSubfulfillment
    }

    ThresholdSubfulfillment ::= SEQUENCE {
      weight INTEGER (0..4294967295) DEFAULT 1,
      condition Condition OPTIONAL,
      fulfillment Fulfillment OPTIONAL
    }


threshold
: is a number and MUST be an integer in the range 1 ... 2^32 - 1. In order to fulfill a threshold condition, the weights of the provided fulfillments MUST be greater than or equal to the threshold.

subfulfillments
: is the set of subconditions and subfulfillments, each provided as a tuple of weight and condition or fulfillment.

weight
: is the numeric weight of this subcondition, i.e. how many times it counts against the threshold. It MUST be an integer in the range 1 ... 2^32 - 1.

condition
: is the subcondition if this subcondition is not fulfilled.

fulfillment
: is the subfulfillment if this subcondition is fulfilled.

### Example {#threshold-sha-256-example}

Example condition:

    cc:2:2b:mJUaGKCuF5n-3tfXM2U81VYtHbX-N8MP6kz8R-ASwNQ:146


Example fulfillment:

    cf:2:AQEBAgEBAwAAAAABAQAnAAQBICDsFyuTrV5WO_STLHDhJFA0w1Rn7y79TWTr-BloNGfivwFg


## RSA-SHA-256 {#rsa-sha-256-condition-type}
RSA-SHA-256 is assigned the type ID 3. It relies on the SHA-256 and RSA-PSS feature suites which corresponds to a feature bitmask of 0x11.

The signature algorithm used is RSASSA-PSS as defined in PKCS#1 v2.2. [RFC3447](#RFC3447)  

### Condition {#rsa-sha-256-condition-type-condition}
The fingerprint of a RSA-SHA-256 condition is the SHA-256 digest of the fingerprint contents given below:

The salt length for PSS is 32 bytes.

    RsaSha256FingerprintContents ::= SEQUENCE {
      modulus OCTET STRING (SIZE(128..512))
    }


modulus
: is an octet string representing the RSA public modulus in big-endian byte order. The first byte of the modulus MUST NOT be zero.

: The corresponding public exponent e is assumed to be 65537 as recommended in [RFC4871](#RFC4871) . Very large exponents can be a DoS vector [LARGE-RSA-EXPONENTS](#LARGE-RSA-EXPONENTS) and 65537 is the largest Fermat prime, which has some nice properties [USING-RSA-EXPONENT-OF-65537](#USING-RSA-EXPONENT-OF-65537) .

: Implementations MUST reject moduli smaller than 128 bytes (1017 bits) or greater than 512 bytes (4096 bits.) Large moduli slow down signature verification which can be a denial-of-service vector. DNSSEC also limits the modulus to 4096 bits [RFC3110](#RFC3110) . OpenSSL supports up to 16384 bits [OPENSSL-X509-CERT-EXAMPLES](#OPENSSL-X509-CERT-EXAMPLES) .


### Fulfillment {#rsa-sha-256-condition-type-fulfillment}

    RsaSha256FulfillmentPayload ::= SEQUENCE {
      modulus OCTET STRING (SIZE(128..512)),
      signature OCTET STRING (SIZE(128..512))
    }


modulus
: is an octet string representing the RSA public modulus in big-endian byte order. See [rsa-sha-256-condition-type-condition](#rsa-sha-256-condition-type-condition)  

signature
: is an octet string representing the RSA signature. It MUST be encoded in big-endian byte order with the exact same number of octets as the modulus, even if this means adding leading zeros. This ensures that the fulfillment size is constant and known ahead of time. Note that the field is still binary encoded with a length prefix for consistency.

: Implementations MUST verify that the signature and modulus consist of the same number of octets and that the signature is numerically less than the modulus.

The message to be signed is provided separately. If no message is provided, the message is assumed to be an octet string of length zero.

### Implementation {#rsa-sha-256-condition-type-implementation}
The recommended modulus size as of 2016 is 2048 bits [KEYLENGTH-RECOMMENDATION](#KEYLENGTH-RECOMMENDATION) . In the future we anticipate an upgrade to 3072 bits which provides approximately 128 bits of security [NIST-KEYMANAGEMENT](#NIST-KEYMANAGEMENT) (p. 64), about the same level as SHA-256.

### Example {#rsa-sha-256-example}

Example condition:

    cc:3:11:Bw-r77AGqSCL0huuMQYj3KW0Jh67Fpayeq9h_4UJctg:260

Example fulfillment:

    cf:3:gYCzDnqTh4O6v4NoUP9J4U-H4_ktXEbjP-yj5PCyI1hYCxF2WZX0uO6n-0cSwuHjFvf3dalT0jIhahadmmTdwAcSCkALN_KvwHe2L-ME3nTeahGexAdrUpxPYJawuq1PUz3wFzubgi_YXWX6S--pLY9ST2nLygE2vYDQlcFprsDglYGAjQM0-Z5B-953uQtJ5dXL1D5TWpM0s0eFF0Zty7J2Y3Nb0PqsR5I47a2wYlA7-106vjC8gHFdHVeSR6JksSrhj8YaMWfV0A6qhPz6hq-TqSKCXd4mf3eCpyyFYR_EyH5zXd56sJEU3snWlFbB_bKAW4si_qdfY9dT87YGUp_Grm0




## ED25519 {#ed25519-condition-type}
ED25519 is assigned the type ID 4. It relies only on the ED25519 feature suite which corresponds to a bitmask of 0x20.

The exact algorithm and encodings used for public key and signature are defined in [I-D.irtf-cfrg-eddsa](#I-D.irtf-cfrg-eddsa) as Ed25519. SHA-512 is used as the hashing function.

Note: This document is not defining the SHA-512 versions of other condition types. In addition, the Ed25519 condition type is already uniquely identified by a corresponding Ed25519 feature suite. Therefore we intentionally do not introduce a SHA-512 feature suite in this document.

### Condition {#ed25519-condition-type-condition}
The fingerprint of a ED25519 condition is the 32 byte Ed25519 public key. Since the public key is already very small, we do not hash it.

### Fulfillment {#ed25519-condition-type-fulfillment}

    Ed25519FulfillmentPayload ::= SEQUENCE {
      publicKey OCTET STRING (SIZE(32)),
      signature OCTET STRING (SIZE(64))
    }


publicKey
: is an octet string containing the Ed25519 public key.

signature
: is an octet string containing the Ed25519 signature.

### Example

Example condition:

    cc:4:20:7Bcrk61eVjv0kyxw4SRQNMNUZ-8u_U1k6_gZaDRn4r8:96

Example fulfillment:

    cf:4:7Bcrk61eVjv0kyxw4SRQNMNUZ-8u_U1k6_gZaDRn4r-2IpH62UMvjymLnEpIldvik_b_2hpo2t8Mze9fR6DHISpf6jzal6P0wD6p8uisHOyGpR1FISer26CdG28zHAcK




--- back

# Security Considerations

This section to be expanded in a later draft. <!-- TODO -->

# Test Values

This section to be expanded in a later draft.  <!-- TODO --> For now, see the test cases for the reference implementation: <https://github.com/interledger/five-bells-condition/tree/master/test>

# ASN.1 Module {#appendix-c}

    --<ASN1.PDU CryptoConditions.Condition, CryptoConditions.Fulfillment>--

    CryptoConditions
    DEFINITIONS
    AUTOMATIC TAGS ::=
    BEGIN

    /**
    * CONTAINERS
    */

    Condition ::= SEQUENCE {
    type ConditionType,
    featureBitmask OCTET STRING,
    fingerprint OCTET STRING,
    maxFulfillmentLength INTEGER (0..MAX)
    }

    Fulfillment ::= SEQUENCE {
    type ConditionType,
    payload OCTET STRING
    }

    ConditionType ::= INTEGER {
    preimageSha256(0),
    rsaSha256(1),
    prefixSha256(2),
    thresholdSha256(3),
    ed25519(4)
    } (0..65535)

    /**
    * FULFILLMENT PAYLOADS
    */

    -- For preimage conditions, the payload equals the preimage

    PrefixSha256FulfillmentPayload ::= SEQUENCE {
    prefix OCTET STRING,
    subfulfillment Fulfillment
    }

    ThresholdSha256FulfillmentPayload ::= SEQUENCE {
    threshold INTEGER (0..4294967295),
    subfulfillments SEQUENCE OF ThresholdSubfulfillment
    }

    ThresholdSubfulfillment ::= SEQUENCE {
    weight INTEGER (0..4294967295) DEFAULT 1,
    condition Condition OPTIONAL,
    fulfillment Fulfillment OPTIONAL
    }

    RsaSha256FulfillmentPayload ::= SEQUENCE {
    modulus OCTET STRING (SIZE(128..512)),
    signature OCTET STRING (SIZE(128..512))
    }

    Ed25519FulfillmentPayload ::= SEQUENCE {
    publicKey OCTET STRING (SIZE(32)),
    signature OCTET STRING (SIZE(64))
    }

    /**
    * FINGERPRINTS
    */

    -- SHA-256 hash of the fingerprint contents
    Sha256Fingerprint ::= OCTET STRING (SIZE(32)) -- digest

    -- 32-byte Ed25519 public key
    Ed25519Fingerprint ::= OCTET STRING (SIZE(32)) -- publicKey

    /**
    * FINGERPRINT CONTENTS
    *
    * The content that will be hashed to arrive at the fingerprint.
    */

    -- The preimage type hashes the raw contents of the preimage

    PrefixSha256FingerprintContents ::= SEQUENCE {
    prefix OCTET STRING,
    condition Condition
    }

    ThresholdSha256FingerprintContents ::= SEQUENCE {
    threshold INTEGER (0..4294967295),
    subconditions SEQUENCE OF ThresholdSubcondition
    }

    ThresholdSubcondition ::= SEQUENCE {
    weight INTEGER (0..4294967295),
    condition Condition
    }

    RsaSha256FingerprintContents ::= INTEGER (0..MAX) -- modulus

    /**
    * EXAMPLES
    */

    exampleCondition Condition ::=
    {
    type preimageSha256,
    featureBitmask '03'H,
    fingerprint '
    E3B0C442 98FC1C14 9AFBF4C8 996FB924 27AE41E4 649B934C A495991B 7852B855
    'H,
    maxFulfillmentLength 2
    }

    exampleFulfillment Fulfillment ::=
    {
    type preimageSha256,
    payload '00'H
    }

    exampleRsaSha256FulfillmentPayload RsaSha256FulfillmentPayload ::=
    {
    modulus '
    B30E7A93 8783BABF 836850FF 49E14F87 E3F92D5C 46E33FEC A3E4F0B2 2358580B
    11765995 F4B8EEA7 FB4712C2 E1E316F7 F775A953 D232216A 169D9A64 DDC00712
    0A400B37 F2AFC077 B62FE304 DE74DE6A 119EC407 6B529C4F 6096B0BA AD4F533D
    F0173B9B 822FD85D 65FA4BEF A92D8F52 4F69CBCA 0136BD80 D095C169 AEC0E095
    'H,
    signature '
    48E8945E FE007556 D5BF4D5F 249E4808 F7307E29 511D3262 DAEF61D8 8098F9AA
    4A8BC062 3A8C9757 38F65D6B F459D543 F289D73C BC7AF4EA 3A33FBF3 EC444044
    7911D722 94091E56 1833628E 49A772ED 608DE6C4 4595A91E 3E17D6CF 5EC3B252
    8D63D2AD D6463989 B12EEC57 7DF64709 60DF6832 A9D84C36 0D1C217A D64C8625
    BDB594FB 0ADA086C DECBBDE5 80D424BF 9746D2F0 C312826D BBB00AD6 8B52C4CB
    7D47156B A35E3A98 1C973863 792CC80D 04A18021 0A524158 65B64B3A 61774B1D
    3975D78A 98B0821E E55CA0F8 6305D425 29E10EB0 15CEFD40 2FB59B2A BB8DEEE5
    2A6F2447 D2284603 D219CD4E 8CF9CFFD D5498889 C3780B59 DD6A57EF 7D732620
    'H
    }

    exampleEd25519FulfillmentPayload Ed25519FulfillmentPayload ::=
    {
    publicKey '
    EC172B93 AD5E563B F4932C70 E1245034 C35467EF 2EFD4D64 EBF81968 3467E2BF
    'H,
    signature '
    B62291FA D9432F8F 298B9C4A 4895DBE2 93F6FFDA 1A68DADF 0CCDEF5F 47A0C721
    2A5FEA3C DA97A3F4 C03EA9F2 E8AC1CEC 86A51D45 2127ABDB A09D1B6F 331C070A
    'H
    }

    END


# IANA Considerations {#appendix-e}

## Crypto-Condition Type Registry {#crypto-conditions-type-registry}

The following initial entries should be added to the Crypto-Condition Type registry to be created and maintained at (the suggested URI)
<http://www.iana.org/assignments/crypto-condition-types>:

The following feature suite bits are registered:

| Type Bit | Exp. | Hex  | Feature         |
|----------|------|------|-----------------|
| 1        | 2^0  | 0x01 | SHA-256         |
| 10       | 2^1  | 0x02 | PREIMAGE        |
| 100      | 2^2  | 0x04 | PREFIX          |
| 1000     | 2^3  | 0x08 | THRESHOLD       |
| 10000    | 2^4  | 0x10 | RSA             |
| 100000   | 2^5  | 0x20 | ED25519         |
{: #crypto-condition-feature-suites title="Crypto-Condition Feature Suites"}

The following types are registered:

| Type ID | Required Bitmask | Type Name         |
|---------|------------------|-------------------|
| 0       | 0x03             | PREIMAGE-SHA-256  |
| 1       | 0x05             | PREFIX-SHA-256    |
| 2       | 0x09             | THRESHOLD-SHA-256 |
| 3       | 0x11             | RSA-SHA-256       |
| 4       | 0x20             | ED25519           |
{: #crypto-condition-types title="Crypto-Condition Types"}
