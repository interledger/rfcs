---
coding: utf-8

title: Crypto-Conditions
docname: draft-thomas-crypto-conditions-02
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

  -
    ins: A. Hope-Bailie
    name: Adrian Hope-Bailie
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: adrian@ripple.com
    uri: https://www.ripple.com

normative:
    RFC3280:
    RFC8017:
    RFC4055:
    RFC4648:
    I-D.draft-irtf-cfrg-eddsa-08:
    itu.X680.2015:
        title: "Information technology – Abstract Syntax Notation One (ASN.1): Specification of basic notation"
        target: http://handle.itu.int/11.1002/1000/12479
        author:
            organization: International Telecommunications Union
        date: 2015-08
        seriesInfo:
            name: "ITU-T"
            value: "Recommendation ITU-T X.680, August 2015"
    itu.X690.2015:
        title: "Information technology – ASN.1 encoding rules: Specification of Basic Encoding Rules (BER), Canonical Encoding Rules (CER) and Distinguished Encoding Rules (DER)"
        target: http://handle.itu.int/11.1002/1000/12483
        author:
            organization: International Telecommunications Union
        date: 2015-08
        seriesInfo:
            name: "ITU-T"
            value: "Recommendation ITU-T X.690, August 2015"

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

This specification is a part of the [Interledger Protocol](https://interledger.org/) work. Feedback related to this specification should be sent to <ledger@ietf.org>.

--- abstract

The crypto-conditions specification defines a set of encoding formats and data structures for **conditions** and **fulfillments**.  A condition uniquely identifies a logical "boolean circuit" constructed from one or more logic gates, evaluated by either validating a cryptographic signature or verifying the preimage of a hash digest. A fulfillment is a data structure encoding one or more cryptographic signatures and hash digest preimages that define the structure of the circuit and provide inputs to the logic gates allowing for the result of the circuit to be evaluated.

A fulfillment is validated by evaluating that the circuit output is TRUE but also that the provided fulfillment matches the circuit fingerprint, the condition.

Since evaluation of some of the logic gates in the circuit (those that are signatures) also take a message as input the evaluation of the entire fulfillment takes an optional input message which is passed to each logic gate as required. As such the algorithm to validate a fulfillment against a condition and a message matches that of other signature schemes and a crypto-condition can serve as a sophisticated and flexible replacement for a simple signature where the condition is used as the public key and the fulfillment as the signature.

--- middle

# Introduction

Crypto-conditions is a scheme for composing signature-like structures from one or more existing signature scheme or hash digest primitives. It defines a mechanism for these existing primitives to be combined and grouped to create complex signature arrangements but still maintain the useful properties of a simple signature, most notably, that a deterministic algorithm exists to verify the signature against a message given a public key.

Using crypto-conditions, existing primitives such as RSA and ED25519 signature schemes and SHA256 digest algorithms can be used as logic gates to construct complex boolean circuits which can then be used as a compound signature. The validation function for these compound signatures takes as input the fingerprint of the circuit, called the condition, the circuit definition and minimum required logic gates with their inputs, called the fulfillment, and a message.

The function returns a boolean indicating if the compound signature is valid or not. This property of crypto-conditions means they can be used in most scenarios as a replacement for existing signature schemes which also take as input, a public key (the condition), a signature (the fulfillment), and a message and return a boolean result.

# Terminology
The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC2119][].

# Types
Crypto-conditions are a standard format for expressing conditions and fulfillments. The format supports multiple algorithms, including different hash functions and cryptographic signing schemes. Crypto-conditions can be nested in multiple levels, with each level possibly having multiple signatures.

The different types of crypto-conditions each have different internal strutures and employ different cryptographic algorithms as primitives.

## Simple and Compound Types

Two categories of crypto-condition type exist. Simple crypto-conditions provide a standard encoding of common cryptographic primitives with hardcoded parameters, e.g RSA and ED25519 signature or SHA256 hash digests. As such, simple types that use the same underlying scheme (e.g. SHA) with different parameters (e.g. 256 or 512 bits) are considered different crypto-condition types.

As an example, the types defined in this version of the specification all use the SHA-256 digest algorithm to generate the condition fingerprint. If a future version were to introduce SHA-512 as an alternative this would require that new types be defined for each existing type that must have its condition generated using SHA-512.

Compound crypto-conditions contain one or more sub-crypto-conditions. The compound crypto-condition will evaluate to TRUE or FALSE based on the output of the evaluation of the sub-crypto-conditions. In this way compound crypto-conditions are used to construct branches of a boolean circuit.

To validate a compound crypto-condition all sub-crypto-conditions are provided in the fulfillment so that the fingerprint of the compound condition can be generated. However, some of these sub-crypto-conditions may be sub-fulfillments and some may be sub-conditions, depending on the type and properties of the compound crypto-condition.

As an example, in the case of an m-of-n signature scheme, only m sub-fulfillments are needed to validate the compound signature, but the remaining n-m sub-conditions must still be provided to validate that the complete fulfillment matches the originally provided condition. This is an important feature for multi-party signing, when not all parties are ready to provide fulfillment yet all parties still desire fulfillment of the overall condition if enough counter-parties do provide fulfillment.

## Defining and Supporting New types

The crypto-conditions format has been designed so that it can be expanded. For example, you can add new cryptographic signature schemes or hash functions. This is important because advances in cryptography frequently render old algorithms insecure or invent newer, more effective algorithms.

Implementations are not required to support all condition types therefore it is necessary to indicate which types an implementation must support in order to validate a fulfillment. For this reason, compound conditions are encoded with an additional field, subtypes, indicating the set of types and subtypes of all sub-crypto-conditions.

#Features

Crypto-conditions offer many of the features required of a regular signature scheme but also others which make them useful in a variety of new use cases.

## Multi-Algorithm

Each condition type uses one or more cryptographic primitives such as digest or signature algorithms. Compound types may contain sub-crypto-conditions of any type and indicate the set of underlying types in the subtypes field of the condition

To verify that a given implementation can verify a fulfillment for a given condition, implementations MUST ensure they are able to validate fulfillments of all types indicated in the subtypes field of a compound condition. If an implementation encounters an unknown type it MUST reject the condition as it will almost certainly be unable to validate the fulfillment.

## Multi-Signature
Crypto-conditions can abstract away many of the details of multi-sign. When a party provides a condition, other parties can treat it opaquely and do not need to know about its internal structure. That allows parties to define arbitrary multi-signature setups without breaking compatibility. That said, it is important that implementations must inspect the ypes and subtypes of any crypto-conditions they encounter to ensure they do not pass on a condition they will not be able to verify at a later stage.

In many instances protocol designers can use crypto-conditions as a drop-in replacement for public key signature algorithms and add multi-signature support to their protocols without adding any additional complexity.

## Multi-Level
Crypto-conditions elegantly support weighted multi-signatures and multi-level signatures. A threshold condition has a number of subconditions, and a target threshold. Each subcondition can be a signature or another threshold condition. This provides flexibility in forming complex conditions.

For example, consider a threshold condition that consists of two subconditions, one each from Wayne and Alf. Alf's condition can be a signature condition while Wayne's condition is a threshold condition, requiring both Claude and Dan to sign for him.

Multi-level signatures allow more complex relationships than simple M-of-N signing. For example, a weighted condition can support an arrangement of subconditions such as, "Either Ron, Mac, and Ped must approve; or Smithers must approve."


## Crypto-conditions as a signature scheme

Crypto-conditions is a signature scheme for compound signatures which has similar properties to most other signature schemes, such as:
  1. Validation of the signature (the fulfillment) is done using a public key (the condition) and a message as input
  2. The same public key can be used to validate multiple different signatures, each against a different message
  3. It is not possible to derive the signature from the public key
  
However, the scheme also has a number of features that make it unique such as:
  1. It is possible to derive the same public key from any valid signature without the message
  2. It is possible for the same public key and message to be used to validate multiple signatures. For example, the fulfillment of an m-of-n condition will be different for each combination of n signatures.
  3. Composite signatures use one or more other signatures as components allowing for recursive signature validation logic to be defined.  
  4. A valid signature can be produced using different combinations of private keys if the structure of the compound signature requires only specific combinations of internal signatures to be valid  (m of n signature scheme).
  
## Crypto-conditions as a trigger in distributed systems

One of the challenges facing a distributed system is achieving atomic execution of a transaction across the system. A common pattern for solving this problem is two-phase commit in which the most time and resource-consuming aspects of the transaction are prepared by all participants following which a simple trigger is sufficient to either commit or abort the transaction. Described in more abstract terms, the system consists of a number of participants that have prepared a transaction pending the fulfillment of a predefined condition.

Crypto-conditions defines a mechanism for expressing these triggers as pairs of unique trigger identifiers (conditions) and cryptographically verifiable triggers (fulfillments) that can be deterministically verified by all participants.

It is also important that all participants in such a distributed system are able to evaluate, prior to the trigger being fired, that they will be capable of verifying the trigger. Determinism is useless if validation of the trigger requires algorithms or resources that are not available to all participants.

Therefore conditions may be used as **distributable event descriptions** in the form of a *fingerprint*, but also *event meta-data* that allows the event verification system to determine if they have the necessary capabilities (such as required crypto-algorithms) and resources (such as heap size or memory) to verify the event notification later.

Fulfillments are therefore **cryptographically verifiable event notifications** that can be used to verify the event occurred but also that it matches the given description.

When using crypto-conditions as a trigger it will often make sense for the message that is used for validation to be empty to match the signature of the trigger processing system's API. This makes crypto-conditions compatible with systems that use simple hash-locks as triggers.

If a PKI signature scheme is being used for the triggers this would require a new key pair for each trigger which is impractical. Therefore the PREFIX compound type wraps a sub-crypto-condition with a message prefix that is applied to the message before signature validation. In this way a unique condition can be derived for each trigger even if the same key pair is re-used with an empty message.

## Smart signatures

In the Interledger protocol, fulfillments provide non-repudiable proof that a transaction has been completed on a ledger. They are simple messages that can be easily shared with other ledgers. This allows ledgers to escrow funds or hold a transfer conditionally, then execute the transfer automatically when the ledger sees the fulfillment of the stated condition. In this way the Interledger protocol synchronizes multiple transfers on distinct ledgers in an almost atomic end-to-end transaction.

Crypto-conditions may also be useful in other contexts where a system needs to make a decision based on predefined criteria, and the proof from a trusted oracle(s) that the criteria have been met, such as smart contracts.

The advantage of using crypto-conditions for such use cases as opposed to a turing complete contract scripting language is the fact that the outcome of a crypto-condition validation is deterministic across platforms as long as the underlying cryptographic primitives are correctly implemented.

# Validation of a fulfillment

Validation of a fulfillment (F) against a condition (C) and a message (M), in the majority of cases, follows these steps: 

1. The implementation must derive a condition from the fulfillment and ensure that the derived condition (D) matches the given condition (C). 

2. If the fulfillment is a simple crypto-condition AND is based upon a signature scheme (such as RSA-PSS or ED25519) then any signatures in the fulfillment (F) must be verified, using the appropriate signature verification algorithm, against the corresponding public key, also provided in the fulfillment and the message (M) (which may be empty).

3. If the fulfillment is a compound crypto-condition then the sub-fulfillments MUST each be validated. In the case of the PREFIX-SHA-256 type the sub-fulfillment MUST be valid for F to be valid and in the case of the THRESHOLD-SHA-256 type the number of valid sub-fulfillments must be equal or greater than the threshold defined in F.

If the derived condition (D) matches the input condition (C) AND the boolean circuit defined by the fulfillment evaluates to TRUE then the fulfillment (F) fulfills the condition (C).

A more detailed validation algorithm for each crypto-condition type is provided with the details of the type later in this document. In each case the notation F.x or C.y implies; the decoded value of the field named x of the fulfillment and the decoded value of the field named y of the Condition respectively.

## Subfulfillments

In validating a fulfillment for a compound crypto-condition it is necessary to validate one or more sub-fulfillments per step 3 above. In this instance the condition for one or more of these sub-fulfillments is often not available for comparison with the derived condition. Implementations MUST skip the first fulfillment validation step as defined above and only perform steps 2 and 3 of the validation.

The message (M) used to validate sub-fulfillments is the same message (M) used to validate F however in the case of the PREFIX-SHA-256 type this is prefixed with F.prefix before validation of the sub-fulfillment is performed.


# Deriving the Condition

Since conditions provide a unique fingerprint for fulfillments it is important that a determinisitic algorithm is used to derive a condition. For each crypto-condition type details are provided on how to:

  1. Assemble the fingerprint content and if neccessary calculate the hash digest of this data.
  2. Calculate the maximum fulfillment length of a fulfillment
  
For compound types the fingerprint content will contain the complete, encoded, condition for all sub-crypto-conditions. Implementations MUST abide by the ordering rules provided when assembling the fingerprint content.

When calculating the fingerprint of a compound crypto-condition implementations MUST first derive the condition for all sub-fulfillments and include these conditions when assembling the fingerprint content.

## Conditions as Public Keys

Since the condition is just a fingerprint and meta-data about the crypto-condition it can be transmitted freely in the same way a public key is shared publicly. It's not possible to derive the fulfillment from the condition.

# Format

A description of crypto-conditions is provided in this document using Abstract Syntax Notation One (ASN.1) as defined in [ITU.X680.2015](#itu.X680.2015).

## Encoding Rules

Implementations of this specificiation MUST support encoding and decoding using Distinguished Encoding Rules (DER) as defined in [ITU.X690.2015](#itu.X690.2015). This is the canonical encoding format.

Alternative encodings may be used to represent top-level conditions and fulfillments but to ensure a determinisitic outcome in producing the condition fingerprint content, including any sub-conditions, MUST be DER encoded prior to hashing (if hashing is required).

## Condition {#condition-format}

The binary encoding of conditions differs based on their type. All types define at least a fingerprint and maxFulfillmentLength sub-field. Some types, such as the compound condition types, define additional sub-fields that are required to convey essential properties of the crypto-condition (such as the sub-types used by sub-conditions in the case of the compound types).

Each crypto-condition type has a type ID. The list of known types is the IANA-maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry).

Conditions are encoded as follows:

    Condition ::= CHOICE {
	  preimageSha256 SimpleCondition,
	  prefixSha256 CompoundCondition,
	  thresholdSha256 CompoundCondition,
	  rsaSha256 SimpleCondition,
	  ed25519 SimpleCondition
    }

    SimpleCondition ::= SEQUENCE {
      fingerprint OCTET STRING (SIZE(32)),
      maxFulfillmentLength INTEGER (0..MAX)
    }

    CompoundCondition ::= SEQUENCE {
      fingerprint OCTET STRING (SIZE(32)),
      maxFulfillmentLength INTEGER (0..MAX),
      subtypes ConditionTypes
    }

    ConditionTypes ::= BIT STRING {
      preImageSha256  (0),
      prefixSha256    (1),
      thresholdSha256 (2),
      rsaSha256       (3),
      ed25519         (4)
    }
    
### Fingerprint

The fingerprint is an octet string uniquely representing the condition with respect to other conditions **of the same type**. 

Implementations which index conditions MUST use the complete encoded condition as the key, not just the fingerprint - as different conditions of different types may have the same fingerprint. 

For most condition types, the fingerprint is a cryptographically secure hash of the data which defines the condition, such as a public key. 

For types that use PKI signature schemes, the signature is intentionally not included in the content that is used to compose the fingerprint. This means the fingerprint can be calculated without needing to know the message or having access to the private key.

Future types may use different functions to produce the fingerprint which may have different lengths therefore the field is encoded as a variable length string.

### MaxFulfillmentLength

This is the maximum length of the fulfillment payload for a fulfillment that can fulfill this condition.

For each crypto-condition type, an algorithm is provided for consistently calculating the maximum fulfillment length to ensure that implementations produce deterministic output.

When a crypto-condition is submitted to an implementation, this implementation MUST verify that it will be able to process a fulfillment with a payload of size maxFulfillmentLength.

### Subtypes

Subtypes is a bitmap that indicates the set of types an implementation must support in order to be able to successfully validate the fulfillment of this condition. This is the set of types and subtypes of all sub-crypto-conditions, recursively. 

It must be possible to verify that all types used in a crypto-condition are supported (including the types and subtypes of any sub-crypto-conditions) even if the fulfillment is not available to be analysed yet. Therefore, all compound conditions set the bits in this bitmap that correspond to the set of types and subtypes of all sub-crypto-conditions.

The field is encoded as a variable length BIT STRING, as defined in ASN.1 to accommodate new types that may be defined. 

Each bit in the bitmap represents a type from the list of known types in the IANA-maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry) and the bit corresponding to each type is the bit at position X where X is the type ID of the type. 

The presence of one or more sub-crypto-conditions of a specific type is indicated by setting the numbered bit corresponding to the type ID of that type.

For example, a compound condition that contains an ED25519 crypto-condition as a sub-crypto-condition will set the bit at position 4. 

Bits are numbered per the encoding rules for the ASN.1 BIT STRING type.

## Fulfillment {#fulfillment-format}

The ASN.1 definition for fulfillments is defined as follows:

    Fulfillment ::= CHOICE {
	  preimage PreimageFulfillment ,
	  prefix PrefixFulfillment,
      threshold ThresholdFulfillment,
	  rsaSha256 RsaSha256Fulfillment,
	  ed25519 Ed25519Fulfillment
    }

    PreimageFulfillment ::= OCTET STRING

    PrefixFulfillment ::= SEQUENCE {
      prefix OCTET STRING,
      subfulfillment Fulfillment
    }

    ThresholdFulfillment ::= SEQUENCE {
      threshold INTEGER (1..65535),
      subfulfillments SEQUENCE OF Fulfillment,
      subconditions SEQUENCE OF Condition
    }

    RsaSha256Fulfillment ::= SEQUENCE {
      publicKey RSAPublicKey,
      signature OCTET STRING
    }

    Ed25519Fulfillment ::= SEQUENCE {
      publicKey OCTET STRING (SIZE(32)),
      signature OCTET STRING (SIZE(64))
    }

    -- IMPORTS from [RFC8017]{#8017}
    RSAPublicKey ::= SEQUENCE {
          modulus INTEGER,  -- n
          publicExponent INTEGER -- e
    }
    
# Crypto-Condition Types {#crypto-condition-types}
The following condition types are defined in this version of the specification. While support for additional crypto-condition types may be added in the future and will be registered in the IANA maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry), no other types are supported by this specification.

## PREIMAGE-SHA-256 {#preimage-sha-256-condition-type}

PREIMAGE-SHA-256 is assigned the type ID 0. It relies on the availability of the SHA-256 digest algorithm.

This type of condition is also called a "hashlock". By creating a hash of a difficult-to-guess 256-bit random or pseudo-random integer it is possible to create a condition which the creator can trivially fulfill by publishing the random value. However, for anyone else, the condition is cryptographically hard to fulfill, because they would have to find a preimage for the given condition hash.

Implementations MUST ignore any input message when validating a PREIMAGE-SHA-256 fulfillment as the validation of this crypto-condition type only requires that the SHA-256 digest of the preimage, taken from the fulfillment, matches the fingerprint, taken from the condition.

### Condition Format {#preimage-sha-256-condition-type-condition}

The fingerprint of a PREIMAGE-SHA-256 condition is the SHA-256 hash of the unencoded preimage. 

### MaxFulfillmentLength {#preimage-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the size, in bytes, of the preimage.

### Fulfillment Format {#preimage-sha-256-condition-type-fulfillment}

    PreimageFulfillment ::= OCTET STRING (SIZE (32))

### Validating {#preimage-sha-256-condition-type-validating}

A PREIMAGE-SHA-256 fulfillment is valid iff C.fingerprint is equal to the SHA-256 hash digest of F.

### Example {#preimage-sha-256-example}

examplePreimageCondition Condition ::= 
  preimageSha256 : 
  {
    fingerprint '7F83B165 7FF1FC53 B92DC181 48A1D65D FC2D4B1F A3D67728 4ADDD200 126D9069'H,
    maxFulfillmentLength 12
  }

DER Encoded 
A025 - CHOICE: preimageSha256 SimpleCondition SEQUENCE: tag = [0] constructed; length 37 bytes;
  8020 - fingerprint OCTET STRING: tag = [0] primitive; length = 32 bytes;
    7F83B165 7FF1FC53 B92DC181 48A1D65D FC2D4B1F A3D67728 4ADDD200 126D9069 - fingerprint value;
  8101 - maxFulfillmentLength INTEGER: tag = [1] primitive; length = 1 byte;
    0C - maxFulfillmentLength value = 12;

examplePreimageFulfillment Fulfillment ::= 
  preimage '48 65 6C 6C 6F 20 57 6F 72 6C 64 21'H

DER Encoded 
  800C - CHOICE: preimage PreimageFulfillment OCTET STRING: tag = [0] primitive; length = 12 bytes;
    4865 6C6C6F20 576F726C 6421 - preimage value: "Hello World!"

## PREFIX-SHA-256 {#prefix-sha-256-condition-type}
PREFIX-SHA-256 is assigned the type ID 1. It relies on the availability of the SHA-256 digest algorithm and any other algorithms required by its sub-crypto-condition as it is a compound crypto-condition type.

Prefix crypto-conditions provide a way to narrow the scope of other crypto-conditions that are used inside the prefix crypto-condition as a sub-crypto-condition. 

Because a condition is the fingerprint of a public key, by creating a prefix crypto-condition that wraps another crypto-condition we can narrow the scope from signing an arbitrary message to signing a message with a specific prefix.

We can also use the prefix condition in contexts where there is an empty message used for validation of the fulfillment so that we can reuse the same key pair for multiple crypto-conditions, each with a different prefix, and therefore generate a unique condition and fulfillment each time.

Implementations MUST prepend the prefix to the provided message and will use the resulting value as the message to validate the sub-fulfillment.

### Condition Format {#prefix-sha-256-condition-type-condition}

The fingerprint of a PREFIX-SHA-256 condition is the SHA-256 digest of the DER encoded fingerprint contents as defined below:

    PrefixSha256ConditionFingerprintContents ::= SEQUENCE {
      prefix OCTET STRING,
      subcondition Condition
    }

prefix
: is an arbitrary octet string which will be prepended to the message during validation.

subcondition
: is the sub-condition derived from the sub-fulfillment.

### MaxFulfillmentLength {#prefix-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the size, in bytes, of the DER encoded prefix, including the tag and length indicator byte(s), plus the maxFulfillmentLength of the sub-crypto-condition.

### Fulfillment Format {#prefix-sha-256-condition-type-fulfillment}

    PrefixFulfillment ::= SEQUENCE {
      prefix OCTET STRING,
      subfulfillment Fulfillment
    }

prefix
: is an arbitrary octet string which will be prepended to the message during validation.

subfulfillment
: is the fulfilled subcondition.

### Validating {#prefix-sha-256-condition-type-validating}

A PREFIX-SHA-256 fulfillment is valid iff:
 
  1. F.subfulfillment is valid, where the message used for validation of F.subfulfillment is M prefixed by F.prefix AND 
  2. D is equal to C. 

### Example {#prefix-sha-256-example}

TODO

## THRESHOLD-SHA-256 {#threshold-sha-256-condition-type}
THRESHOLD-SHA-256 is assigned the type ID 2. It relies on the availability of the SHA-256 digest algorithm and any other algorithms required by any of its sub-crypto-conditions as it is a compound crypto-condition type.

### Condition Format {#threshold-sha-256-condition-type-condition}

The fingerprint of a THRESHOLD-SHA-256 condition is the SHA-256 digest of the DER encoded fingerprint contents given below:

    ThresholdSha256FingerprintContents ::= SEQUENCE {
      threshold INTEGER (0..65535),
      subconditions SEQUENCE OF Condition
    }

threshold
: threshold MUST be an integer in the range 0 ... 65535. In order to fulfill a threshold condition, the number of valid sub-fulfillments MUST be greater than or equal to the threshold.

subconditions
: is the set of sub-conditions.

: The list of DER encoded sub-conditions is sorted first based on encoded length, shortest first. Elements of the same length are sorted in lexicographic (big-endian) order, smallest first.  


### MaxFulfillmentLength {#threshold-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the the sum of the F.threshold largest maxFulfillmentLength values of all sub-conditions where, added to the size of the encoded length of the remaining sub-conditions and the encoded length of the threshold value.

For example, if a threshold crypto-condition contains 5 sub-conditions with maxFulfillment lengths of 64 bytes, 64 bytes, 82 bytes, 84 bytes and 84 bytes and encoded sizes of 34 bytes, 34 bytes, 34 bytes, 68 bytes and 68 bytes respectively and has a threshold of 3, the maxfulfillmentlength is equal to the sum of the largest three sub-condition maxfulfillmentlengths (82 + 84 + 84) plus the lengths of the remaining conditions (34 + 34) plus the encoded lenght of the threshold (3): 321 bytes

Implementations SHOULD provide only the number of sub-fulfillments required by the threshold as providing more may result in the fulfillment length exceeding the stated maxFulfillmentLength.

### Fulfillment Format {#threshold-sha-256-condition-type-fulfillment}

    ThresholdFulfillment ::= SEQUENCE {
      threshold INTEGER (1..65535),
      subfulfillments SEQUENCE OF Fulfillment,
      subconditions SEQUENCE OF Condition
    }

threshold
: is a number and MUST be an integer in the range 1 ... 65535. In order to fulfill a threshold condition, the count of the provided fulfillments MUST be greater than or equal to the threshold.

subfulfillments
: is the set of sub-fulfillments.

subconditions
: is the set of sub-conditions provided in place of any unfulfilled sub-fulfillment.

### Validating {#threshold-sha-256-condition-type-validating}

A THRESHOLD-SHA-256 fulfillment is valid iff :
 
  1. The number of valid F.subfulfillments is equal to or greater than F.threshold.
  2. D is equal to C.

For each subfulfillment the subfulfillment is validated against the message, and the subcondition for that fulfillment is derived. When all subfulfillments have been processed the derived subconditions and the provided subconditions are combined and sorted as defined by the condition formatting rules and the fingerprint and condition (D) is derived from the sequence of these subconditions.

### Example {#threshold-sha-256-example}

TODO

## RSA-SHA-256 {#rsa-sha-256-condition-type}
RSA-SHA-256 is assigned the type ID 3. It relies on the SHA-256 digest algorithm and the RSA-PSS signature scheme.

The signature algorithm used is RSASSA-PSS as defined in PKCS#1 v2.2. [RFC8017](#RFC8017)  

Implementations MUST NOT use the default RSASSA-PSS-params. Implementations MUST use the SHA-256 hash algorithm and therefore, the same algorithm in the mask generation algorithm, as recommended in [RFC8017](#RFC8017). The algorithm parameters to use, as defined in [RFC4055](#RFC4055) are:

    pkcs-1 OBJECT IDENTIFIER  ::=  { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 1 }

    id-sha256 OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 1 }
    
    sha256Identifier AlgorithmIdentifier  ::=  {
      algorithm id-sha256,
      parameters nullParameters  
    }
                              
    id-mgf1 OBJECT IDENTIFIER  ::=  { pkcs-1 8 }                          
                              
    mgf1SHA256Identifier AlgorithmIdentifier  ::=  {
      algorithm id-mgf1,
      parameters sha256Identifier 
    }
    
    rSASSA-PSS-SHA256-Params RSASSA-PSS-params ::=  {
      hashAlgorithm sha256Identifier,
      maskGenAlgorithm mgf1SHA256Identifier,
      saltLength 20,
      trailerField 1
    }

### Condition Format {#rsa-sha-256-condition-type-condition}
The fingerprint of a RSA-SHA-256 condition is the SHA-256 digest of the DER encoded fingerprint contents given below:

    RSASha256FingerprintContents ::= RSAPublicKey

    -- IMPORTS from [RFC8017]{#8017}
    RSAPublicKey ::= SEQUENCE {
          modulus INTEGER,  -- n
          publicExponent INTEGER -- e
    }

modulus
: the RSA public modulus n.

: Implementations MUST reject moduli smaller than 128 bytes (1017 bits) or greater than 512 bytes (4096 bits.) Large moduli slow down signature verification which can be a denial-of-service vector. DNSSEC also limits the modulus to 4096 bits [RFC3110](#RFC3110). OpenSSL supports up to 16384 bits [OPENSSL-X509-CERT-EXAMPLES](#OPENSSL-X509-CERT-EXAMPLES).

publicExponent
: The corresponding publicExponent e is constrained to be the value 65537 as recommended in [RFC4871](#RFC4871). Very large exponents can be a DoS vector [LARGE-RSA-EXPONENTS](#LARGE-RSA-EXPONENTS) and 65537 is the largest Fermat prime, which has some nice properties [USING-RSA-EXPONENT-OF-65537](#USING-RSA-EXPONENT-OF-65537). This constraint is not reflected in the ASN.1 definition as this would affect the encoding but MUST be enforced by implementations.

### MaxFulfillmentLength {#rsa-sha-256-condition-type-maxfulfillmentlength}

The MaxFulfillmentLength is the sum of the encoded length of the publicKey and the signature. The signature MUST be the same encoded length as the publicKey.modulus (even if this means adding leading zeros) therefor it is possible to calculate the MaxFulfillmentLength using just the public key.

### Fulfillment Format {#rsa-sha-256-condition-type-fulfillment}

    RsaSha256FulfillmentPayload ::= SEQUENCE {
      publicKey RSAPublicKey,
      signature OCTET STRING
    }

publicKey
: is the DER encoded RSA public key 

signature
: is an octet string representing the RSA signature. It MUST be encoded in big-endian byte order. with the exact same number of octets as the modulus of the public key, even if this means adding leading zeros. This ensures that the fulfillment size is constant and known ahead of time. Note that the field is still binary encoded with a length prefix for consistency.

: Implementations MUST verify that the signature and modulus consist of the same number of octets and that the signature is numerically less than the modulus.

The message to be signed is provided separately. If no message is provided, the message is assumed to be an octet string of length zero.

### Implementation {#rsa-sha-256-condition-type-implementation}
The recommended modulus size as of 2016 is 2048 bits [KEYLENGTH-RECOMMENDATION](#KEYLENGTH-RECOMMENDATION). In the future we anticipate an upgrade to 3072 bits which provides approximately 128 bits of security [NIST-KEYMANAGEMENT](#NIST-KEYMANAGEMENT) (p. 64), about the same level as SHA-256.

### Validating {#rsa-sha-256-condition-type-validating}

An RSA-SHA-256 fulfillment is valid iff :
 
  1. F.signature is valid for the message M, given the RSA public key F.publicKey.
  2. D is equal to C. 

### Example {#rsa-sha-256-example}

TODO

## ED25519 {#ed25519-condition-type}
ED25519 is assigned the type ID 4. It relies on the SHA-512 digest algorithm and the ED25519 signature scheme as the condition fingerprint is not a digest.

The exact algorithm and encodings used for the public key and signature are defined in [I-D.irtf-cfrg-eddsa](#I-D.irtf-cfrg-eddsa) as Ed25519. SHA-512 is used as the hashing function for this signature scheme.

### Condition Format {#ed25519-condition-type-condition}

The fingerprint of an ED25519 condition is the 32 byte Ed25519 public key. Since the public key is already very small and constant size, we do not hash it.

Ed25519FingerprintContents ::= OCTET STRING (SIZE(32))

### MaxFulfillmentLength {#ed25519-condition-type-maxfulfillmentlength}

The public key and signature are a fixed size therefore the max fulfillment length for an ED25519 crypto-condition is fixed at .

### Fulfillment {#ed25519-condition-type-fulfillment}

    Ed25519Fulfillment ::= SEQUENCE {
      publicKey OCTET STRING (SIZE(32)),
      signature OCTET STRING (SIZE(64))
    }

publicKey
: is an octet string containing the Ed25519 public key.

signature
: is an octet string containing the Ed25519 signature.

### Validating {#ed25519-sha-256-condition-type-validating}

An ED25519 fulfillment is valid iff :
 
  1. F.signature is valid for the message M, given the ED25519 public key F.publicKey.
  2. D is equal to C. 

### Example

# URI Encoding Rules {#uri-encoding-rules}

Implementations MUST support these encoding rules for encoding conditions and fulfillments as URIs. The URI encoding is only used to encode top-level conditions and fulfillments and never for sub-conditions and sub-fulfillments. The binary encoding is considered the canonical encoding.

The following types are defined for the URI encoding:

BASE10
: Variable-length integer encoded as a base-10 (decimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows.

BASE16
: Variable-length integer encoded as a base-16 (hexadecimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows. Encodings may have an odd number of characters as the encoding excludes leading zeros.

BASE64URL
: Base64-URL encoding. See [RFC4648](#RFC4648), Section 5.

## Condition URI Format {#string-condition-format}

Conditions are ASCII encoded as per the ASN.1 data structure with a URI scheme of "cc" and the following encoding rules for invidual fields, whicha re each separated by the colon (":") character:

  1. The CHOICE ASN.1 type is represented by the type name from the [Crypto-Condition Type Registry](#crypto-conditions-type-registry). The convention is to encode this value in lowercase but since URIs are not case sensitive this is not a normative requirement and implementations MUST accept values in any case.

  2. The fingerprint field, defined as an OCTET STRING in ASN.1 is encoded as a BASE64URL string for the URI.

  3. The maxFulfillmentLength field, defined as an INTEGER in ASN.1 is encoded as a BASE10 string representation of the number.

  4. The subtypes field, present for compound crypto-condition types, is represented as a comma separated list of the type names of all sub-types.

The resulting encoding looks as follows for a simple condition:
    "cc:" type-name ":" BASE64URL(fingerprint) ":" BASE10(maxFulfillmentLength)

And as follows for a compound condition:    
    "cc:" type-name ":" BASE64URL(fingerprint) ":" BASE10(maxFulfillmentLength) ":" subtype-name1,subtype-name2,subtype-nameN 

### Example Condition

An example condition (PREIMAGE-SHA-256):

    0x00000000 A0 25 80 20 7F 83 B1 65 7F F1 FC 53 B9 2D C1 81 .%.....e...S.-..
    0x00000010 48 A1 D6 5D FC 2D 4B 1F A3 D6 77 28 4A DD D2 00 H..].-K...w(J...
    0x00000020 12 6D 90 69 81 01 0C                            .m.i...
    
    cc:preimage-sha-256:f4OxZX_x_FO5LcGBSKHWXfwtSx-j1ncoSt3SABJtkGk:12

The example has the following attributes:

| Field                | Value | Description |
|----------------------|-------|----------------------------------------------|
| preface              | `cc`  | Constant. Indicates this is a condition. |
| type                 | `preimage-sha-256`   | This is a [PREIMAGE-SHA-256][] condition. |
| fingerprint          | `f4OxZX_x_FO5LcGBSKHWXfwtSx-j1ncoSt3SABJtkGk` | The fingerprint for this condition. |
| maxFulfillmentLength | `12`  | The fulfillment payload is 12 bytes long, before being BASE64URL-encoded. |

### Fulfillment URI Format {#string-fulfillment-format}

Fulfillments are ASCII encoded as:

    "cf:" BASE64URL(DER encoded fulfillment)

### Example Fulfillment

The following is an example fulfillment in string format, for the [example condition](#example-condition):

    cf:gAxIZWxsbyBXb3JsZCE

The example has the following attributes:

| Field         | Value | Description |
|---------------|-------|----------------------------------------------|
| preface       | `cf`  | Constant. Indicates this is a fulfillment. |
| fulfillment   | `gAxIZWxsbyBXb3JsZCE` | The BASE64URL-encoded fulfillment. |

--- back

# Security Considerations

This specification has a normative dependency on a number of other specifications with extensive security considerations therefore the consideratons defined for SHA-256 hashing and RSA signatures in [RFC8017]{#RFC8017} and [RFC4055]{#RFC4055} and for ED25519 signatures in [I-D.irtf-cfrg-eddsa]{#I-D.irtf-cfrg-eddsa} must be considered.

The MaxFulfillmentLength and subtypes values of conditions are provided to allow implementations to evaluate their ability to validate a fulfillment for the given condition later. Implementations must ensure that processing a fulfillment of the specified size will not result in any overflow errors that may introduce security risks.

# Test Values

This section to be expanded in a later draft.  <!-- TODO --> 

For now, see the test cases for the reference implementation: <https://github.com/interledger/five-bells-condition/tree/master/test>

# ASN.1 Module {#appendix-c}

    --<ASN1.PDU CryptoConditions.Condition, CryptoConditions.Fulfillment>--

    CryptoConditions
    DEFINITIONS
    AUTOMATIC TAGS ::=
    BEGIN
    
    IMPORTS

    AlgorithmIdentifier
      FROM PKIX1Explicit88 -- Found in [RFC3280](#RFC3280)
        { iso(1) identified-organization(3) dod(6) internet(1) security(5) mechanisms(5) pkix(7) id-mod(0) id-pkix1-explicit(18) } ;
    
    
    IMPORTS

    pkcs-1, id-sha256, sha256Identifier, id-mgf1, mgf1SHA256Identifier, RSAPublicKey, rSASSA-PSS-SHA256-Identifier, rSASSA-PSS-SHA256-Params
      FROM PKIX1-PSS-OAEP-Algorithms -- Found in [RFC4055](#RFC4055)
        { iso(1) identified-organization(3) dod(6) internet(1) security(5) mechanisms(5) pkix(7) id-mod(0) id-mod-pkix1-rsa-pkalgs(33) } ;

    Condition ::= CHOICE {
	  preimageSha256 SimpleCondition,
	  prefixSha256 CompoundCondition,
	  thresholdSha256 CompoundCondition,
	  rsaSha256Condition SimpleCondition,
	  ed25519Condition SimpleCondition
    }

    SimpleCondition ::= SEQUENCE {
      fingerprint OCTET STRING (SIZE(32)),
      maxFulfillmentLength INTEGER (0..MAX)
    }

    CompoundCondition ::= SEQUENCE {
      fingerprint OCTET STRING (SIZE(32)),
      maxFulfillmentLength INTEGER (0..MAX),
      subtypes ConditionTypes
    }

    ConditionTypes ::= BIT STRING {
      preImageSha256  (0),
      prefixSha256    (1),
      thresholdSha256 (2),
      rsaSha256       (3),
      ed25519         (4)
    }

    Fulfillment ::= CHOICE {
	  preimage PreimageFulfillment ,
	  prefix PrefixFulfillment,
      threshold ThresholdFulfillment,
	  rsaSha256 RsaSha256Fulfillment,
	  ed25519 Ed25519Fulfillment
    }

    PreimageFulfillment ::= OCTET STRING

    PrefixFulfillment ::= SEQUENCE {
      prefix OCTET STRING,
      subfulfillment Fulfillment
    }

    ThresholdFulfillment ::= SEQUENCE {
      threshold INTEGER (1..65535),
      subfulfillments SEQUENCE OF Fulfillment,
      subconditions SEQUENCE OF Condition
    }

    RsaSha256Fulfillment ::= SEQUENCE {
      publicKey RSAPublicKey,
      signature OCTET STRING
    }

    Ed25519Fulfillment ::= SEQUENCE {
      publicKey OCTET STRING (SIZE(32)),
      signature OCTET STRING (SIZE(64))
    }


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
      threshold INTEGER (0..65535),
      subconditions SEQUENCE OF Condition,
    }

    RsaSha256FingerprintContents ::= RSAPublicKey


    
    /**
    * EXAMPLES
    */

    examplePreimageCondition Condition ::= 
      preimageSha256 : 
      {
        fingerprint '7F83B165 7FF1FC53 B92DC181 48A1D65D FC2D4B1F A3D67728 4ADDD200 126D9069'H,
        maxFulfillmentLength 12
      }


    /**
    * DER Encoded 
    *
    * A0 25 - CHOICE: preimageSha256 SimpleCondition SEQUENCE: tag = [0] constructed; length 37 bytes;
    *    80 20 - fingerprint OCTET STRING: tag = [0] primitive; length = 32 bytes;
    *      7F83B165 7FF1FC53 B92DC181 48A1D65D FC2D4B1F A3D67728 4ADDD200 126D9069 - fingerprint value;
    *    81 01 - maxFulfillmentLength INTEGER: tag = [1] primitive; length = 1 byte;
    *      0C - maxFulfillmentLength value = 12;
    *
    */

    examplePreimageFulfillment Fulfillment ::= 
      preimage '48 65 6C 6C 6F 20 57 6F 72 6C 64 21'H

    /**
    * DER Encoded 
    *
    * 80 0C - CHOICE: preimage PreimageFulfillment OCTET STRING: tag = [0] primitive; length = 12 bytes;
    *    4865 6C6C6F20 576F726C 6421 - preimage value: "Hello World!"


    END

# IANA Considerations {#appendix-e}

## Crypto-Condition Type Registry {#crypto-conditions-type-registry}

The following initial entries should be added to the Crypto-Condition Type registry to be created and maintained at (the suggested URI)
<http://www.iana.org/assignments/crypto-condition-types>:

The following types are registered:

| Type ID | Type Name         |
|---------|-------------------|
| 0       | PREIMAGE-SHA-256  |
| 1       | PREFIX-SHA-256    |
| 2       | THRESHOLD-SHA-256 |
| 3       | RSA-SHA-256       |
| 4       | ED25519           |
{: #crypto-condition-types-table title="Crypto-Condition Types"}
