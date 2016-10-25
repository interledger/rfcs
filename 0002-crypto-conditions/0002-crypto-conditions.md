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

This specification is a part of the [Interledger Protocol](https://interledger.org/) work. Feedback related to this specification should be sent to <ledger@ietf.org>.

--- abstract

Crypto-conditions defines a set of encoding formats and data structures for conditions and fulfillments.  A condition uniquely identifies a boolean circuit constructed from one or more logic gates, evaluated by either validating a cryptographic signature or verifying the preimage of a hash digest. A fulfillment is a data structure encoding one or more cryptographic signatures and hash digest preimages that can be used to evaluate the result of the circuit.

A fulfillment is validated by evaluating the circuit but also verifying that the provided fulfillment matches the circuit fingerprint, the condition.

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

The different structures of different crypto-conditions and the algorithms they employ is defined by the type of the crypto-condition.

## Simple and Compound Types

Two categories of crypto-condition type exist. Simple crypto-conditions provide a standard encoding for existing primitives such as RSA and ED25519 signatures, or SHA256 hash digests where many of the scheme parameters have hardcoded values. As such multiple simple types maybe be defined to encode the same underlying scheme but where the parameters differ.

As an example, the types defined in this version of the specification all use the SHA-256 digest algorithm for derivation of the condition fingerprint. If a future version were to introduce SHA-512 as an alternative this would require that new types be defined for each existing type that must have its condition derived using SHA-512.

Compound crypto-conditions contain one or more sub-crypto-conditions. Compound crypto-conditions are used to construct the branches of the boolean circuit where a compound condition will evaluate to TRUE or FALSE based on the output of the evaluation of their sub-crypto-conditions. 

A compound crypto-condition may have multiple branches and be defined to evaluate to TRUE even if only a subset of these evaluate to TRUE (as in an m-of-n signature scheme). As such the valid fulfillment of a compound condition could contain a combination of sub-fulfillments (that can be evaluated) but also sub-conditions that are simply used (in combination with the derived conditions from the sub-fulfillments) to derive the compound condition and compare this to the condition provided for validation.

## Defining and supporting New types

The crypto-conditions format has been designed so that it can be expanded. For example, you can add new cryptographic signature schemes or hash functions. This is important because advances in cryptography frequently render old algorithms insecure or invent newer, more effective algorithms.

Implementations are not required to support all condition types therefor it is necessary to indicate which types an implementation must support in order to validate a fulfillment. For this reason, compound conditions are encoded with an additional field, subtypes, indicating the set of types and subtypes of all sub-crypto-conditions.

#Features

Crypto-conditions offer many of the features required of a regular signature scheme but also others which make them useful in a variety of new use cases.

## Multi-Algorithm

Each condition type uses one or more cryptographic primitives such as digest or signature algorithms. Compound types may contain sub-crypto-conditions of any type and indicate the set of underlying types in the subtypes field of the condition

To verify that a given implementation can verify a fulfillment for a given condition, implementations MUST ensure they are able to validate fulfillments of all types indicated in the subtypes field of a compound condition. If an implementation encounters an unknown type it MUST reject the condition as it will almost certainly be unable to validate the fulfillment.

## Multi-Signature
Crypto-conditions can abstract away many of the details of multi-sign. When a party provides a condition, other parties can treat it opaquely and do not need to know about its internal structure. That allows parties to define arbitrary multi-signature setups without breaking compatibility.

Protocol designers can use crypto-conditions as a drop-in replacement for public key signature algorithms and add multi-signature support to their protocols without adding any additional complexity.

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
  4. Composite signatures use one or more other signatures as components allowing for recursive signature validation logic to be defined.  
  3. A valid signature can be produced using different combinations of private keys if the structure of the compound signature requires only specific combinations of internal signatures to be valid  (m of n signature scheme).
  
## Crypto-conditions as a trigger in distributed systems

One of the challenges facing a distributed system is achieving atomic execution of a transaction across the system. A common pattern for solving this problem is two-phase commit in which the most time and resource-consuming aspects of the transaction are prepared by all participants following which a simple trigger is sufficient to either commit or abort the transaction. Described in more abstract terms, the system consists of a number of participants that have prepared a transaction pending the fulfillment of a predefined condition.

Crypto-conditions defines a mechanism for expressing these triggers as pairs of unique trigger identifiers (conditions) and cryptographically verifiable triggers (fulfillments) that can be deterministically verified by all participants.

It is also important that all participants in such a distributed system are able to evaluate, prior to the trigger being fired, that they will be capable of verifying the trigger. Determinism is useless if validation of the trigger requires algorithms or resources that are not available to all participants.

Therefor conditions may be used as **distributable event descriptions** in the form of a *fingerprint*, but also *event meta-data* that allows the event verification system to determine if they have the necessary capabilities (such as required crypto-algorithms) and resources (such as heap size or memory) to verify the event notification later.

Fulfillments are therefor **cryptographically verifiable event notifications** can be used to verify that the event occurred but also matches the given description.

When using crypto-conditions as a trigger it will often make sense for the message that is used for validation to be empty to match the signature of the trigger processing system's API. This makes crypto-conditions compatible with systems that use simple hash-locks as triggers.

If a PKI signature scheme is being used for the triggers this would require a new key pair for each trigger which is impractical. Therefor the PREFIX compound type wraps a sub-crypto-condition with a message prefix that is applied to the message before signature validation. In this way a unique condition can be derived for each trigger even if the same key pair is re-used with an empty message.

## Smart signatures

In the Interledger protocol, fulfillments provide irrepudiable proof that a transaction has been completed on a ledger. They are simple messages that can be easily shared with other ledgers. This allows ledgers to escrow funds or hold a transfer conditionally, then execute the transfer automatically when the ledger sees the fulfillment of the stated condition. In this way the Interledger protocol synchronizes multiple transfers on distinct ledgers in an almost atomic end-to-end transaction.

Crypto-conditions may also be useful in other contexts where a system needs to make a decision based on predefined criteria, and the proof from a trusted oracle(s) that the criteria have been met, such as smart contracts.

The advantage of using crypto-conditions for such use cases as opposed to a turing complete contract scripting language is the fact that the outcome of a crypto-condition validation is deterministic across platforms as long as the underlying cryptographic primitives are correctly implemented.

# Validation of a fulfillment

Validation of a fulfillment (F) against a condition (C) and a message (M), in the majority of cases, the following steps. 

1. The implementation must derive a condition from the fulfillment and ensure that the derived condition (D) matches the given condition (C). 

2. If the fulfillment is a simple crypto-condition AND is based upon a signature scheme (such as RSA-PSS or ED25519) then any signatures in the fulfillment (F) must be verified, using the appropriate signature verification algorithm, against the corresponding public key, also provided in the fulfillment and the message (M) (which may be empty).

3. If the fulfillment is a compound crypto-condition then the sub-fulfillments MUST each be validated. In the case of the PREFIX-SHA-256 type the sub-fulfillment MUST be valid for F to be valid and in the case of the THRESHOLD-SHA-256 type the number of valid sub-fulfillments must be equal or greater than the threshold defined in F.

If the derived condition (D) matches the input condition (C) AND the boolean circuit defined by the fulfillment evaluates to TRUE then the fulfillment (F) fulfills the condition (C).

A more detailed validation algorithm for each crypto-condition type is provided with the details of the type later in this document. In each case the notation F.x or C.y implies; the decoded value of the field named x of the fulfillment and the decoded value of the field named y of the Condition respectively.

## Subfulfillments

In validating a fulfillment for a compound crypto-condition it is necessary to validate one or more sub-fulfillments per step 3 above. In this instance the condition for one or more of these sub-fulfillments is often not available for comparison with the derived condition. Implementations MUST skip the first fulfillment validation step as defined above and only perform steps 2 and 3 of the validation.

The message (M) used to validate sub-fulfillments is the same message (M) used to validate F howvere in the case of the PREFIX-SHA-256 type this is prefixed with F.prefix before validation of the sub-fulfillment is performed.


# Deriving the Condition

Since conditions provide a unique fingerprint for fulfillments it is important that a determinisitic algorithm is used to derive a condition. For each crypto-condition type details are provided on how to:

  1. Assemble the fingerprint content and if neccessary calculate the hash digest of this data.
  2. Calculate the maximum fulfillment length of a fulfillment
  
For compound types the fingerprint content will contain the complete, encoded, condition for all sub-crypto-conditions. Implementations MUST abide by the ordering rules provided when assembling the fingerprint content.

When calculating the fingerprint of a compound crypto-condition implementations MUST first derive the condition for all sub-fulfillments and include these conditions when assembling the fingerprint content.

## Conditions as Public Keys

Since the condition is just a fingerprint and meta-data about the crypto-condition it can be transmitted freely in the same way a public key is shared publicly. It's not possible to derive the fulfillment from the condition.

# Format

A description of crypto-conditions is provided in this document using Abstract Syntax Notation One (ASN.1) as defined in [ITU.X680.2015](#itu.X680.2015). Implementations of this spec MUST support encoding and decoding using Octet Encoding Rules (OER) as defined in [ITU.X696.2015](#itu.X696.2015).

## Condition {#condition-format}

The binary encoding of conditions is dependant on their type. The overall size of conditions is not fixed as some types (compound conditions) contain additional fields (subtypes) and the algorithm for deriving the fingerprint differs by type therefor the fingerprint size also differs.

Conditions are encoded as follows:

    Condition ::= SEQUENCE {
      type ConditionType,
      fingerprint OCTET STRING,
      maxFulfillmentLength INTEGER (0..MAX),
      subtypes OCTET STRING
    }

    ConditionType ::= INTEGER {
      preimageSha256(0),
      prefixSha256(1),
      thresholdSha256(2),
      rsaSha256(3),
      ed25519(4)
    } (0..255)

### Type

Type is the numeric type identifier representing the condition type. In future new types may introduce new formats.
    
### Fingerprint

The fingerprint is an octet string uniquely representing the condition with respect to other conditions of the same type. 

Implementations which index conditions MUST use the entire encoded condition as the key, not just the fingerprint - as different conditions of different types may have the same fingerprint. 

For most condition types, the fingerprint is a cryptographically secure hash of the data which defines the condition, such as a public key. 

For types that use PKI signature schemes, the signature is intentionally not included in the content that is used to compose the fingerprint. This meansthe fingerprint can be calculated without needing to know the message or having access to the private key.

Future types may use different functions to produce the fingerprint which may have different lengths therefor the filed is encoded as a variable length string.

### MaxFulfillmentLength

This is the maximum length of the essential fulfillment payload for a fulfillment that can fulfill this condition.

For each crypto-condition type, a formula is provided for calculating the maximum fulfillment length to ensure that implementations produce consistent output.

When a crypto-condition is submitted to an implementation, this implementation MUST verify that it will be able to process a fulfillment with a payload of size maxFulfillmentLength plus any additional encoding bytes.

### Subtypes

It must be possible to verify that all types used in a crypto-condition are supported (including the types and subtypes of any sub-crypto-conditions) even if the fulfillment is not available yet. Therefore, all compound conditions popluate a bitmap to indicate the set of types and subtypes of all sub-crypto-conditions. The subtypes field is only used in the compound conditions (THRESHOLD-SHA-256 and PREFIX-SHA-256), for simple conditions this field should be an empty string.
 
Implementations that encounter a condition with any of the simple types (PREIMAGE-SHA-256, RSA-SHA-256 or ED25519) and a sutypes field that is not an emtpty string MUST reject the condition.

The field is encoded as a variable length octet string. It specifies the set of types an implementation must support in order to be able to successfully validate the fulfillment of this condition. This is the set of types and subtypes of the top-level condition and all sub-crypto-conditions, recursively. 

Each bit in the bitmap represents a type. The list of known types is the IANA-maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry) and the bit corresponding to each type is the bit at position X where X is the type ID of the type. The presence of one of more sub-crypto-conditions of a specific type is indicated by setting the numbered bit corresponding to the type ID of that type.

For example, a compound condition that contains an ED25519 crypto-condition as a sub-crypto-condition will set the bit at position 4. 

Bits are numbered from the least significant bit of the first byte (position 0) to the most significant bit (position 7) and then again from the least significant bit of the next byte (position 8) to the most significant bit (position 15) an so on for all bytes in the bitmap.

#### Examples

The following bitmap indicates the presence of the subtypes PREIMAGE-SHA-256 (type number 0) and RSA-SHA-256 (type number 3)

    Hex
    1       
    0x09
    
    Binary
    7       0          
    0000 1001   
    
The following bitmap indicates the presence of the subtype ED25519 (type number 4)

    Hex
    1        
    0x10 
    
    Binary
    7       0            
    0001 0000  
    
The following bitmap indicates the presence of an unknown subtype with type number 10.

    Hex
    1    2       
    0x00 0x04
    
    Binary
    7       0  15       8            
    0000 0000   0000 0100   

## Fulfillment {#fulfillment-format}

Like conditions, the binary encoding of fulfillments is dependant on their type. 
Unlike conditions there is little commonality between types, the only common field being the type which is encoded in the first byte.

Therefor the ASN.1 definition for fulfillments is defined as follows and the format of the payload is defined per type:

    Fulfillment ::= SEQUENCE {
      type ConditionType,
      payload OCTET STRING,
    }

# Crypto-Condition Types {#crypto-condition-types}
The following condition types are defined in this version of the specification. Future versions of this spec MAY introduce new feature suites and condition types, which SHALL be registered in the IANA maintained [Crypto-Condition Type Registry](#crypto-conditions-type-registry).

## PREIMAGE-SHA-256 {#preimage-sha-256-condition-type}

PREIMAGE-SHA-256 is assigned the type ID 0. It relies on the availability of the SHA-256 digest algorithm.

This type of condition is also called a "hashlock". By creating a hash of a difficult-to-guess 256-bit random or pseudo-random integer it is possible to create a condition which the creator can trivially fulfill by publishing the random value. However, for anyone else, the condition is cryptographically hard to fulfill, because they would have to find a preimage for the given condition hash.

Implementations MUST ignore any input message when validating a PREIMAGE-SHA-256 fulfillment as the validation of this crypto-condition type only requires that the SHA-256 digest of the preimage, taken from the fulfillment, matches the fingerprint, taken from the condition.

### Condition Format {#preimage-sha-256-condition-type-condition}

The fingerprint of a PREIMAGE-SHA-256 condition is the SHA-256 hash of the preimage. 

### MaxFulfillmentLength {#preimage-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the size, in bytes, of the preimage.

### Fulfillment Format {#preimage-sha-256-condition-type-fulfillment}

The fulfillment payload is simply the preimage.

### Validating {#preimage-sha-256-condition-type-validating}

A PREIMAGE-SHA-256 fulfillment is valid iff C.fingerprint is equal to the SHA-256 hash digest of F.preimage.

### Example {#preimage-sha-256-example}

TODO

## PREFIX-SHA-256 {#prefix-sha-256-condition-type}
PREFIX-SHA-256 is assigned the type ID 1. It relies on the availability of the SHA-256 digest algorithm and is a compound crypto-condition type.

Prefix crypto-conditions provide a way to effectively narrow the scope of other crypto-conditions. 

A condition is the fingerprint of a public key used to sign an arbitrary message. By creating a prefix crypto-condition that wraps another condition we can narrow the scope from signing an arbitrary message to signing a message with a specific prefix.

We can also use the prefix condition in contexts where there is an empty message used for validation of the fulfillment so that we can reuse the same key pair for multiple fulfillments, each with a different prefix, and therefore generate a unique condition each time.

Implementations MUST prepend the prefix to the provided message and will use the resulting value as the message to validate the sub-fulfillment.

### Condition Format {#prefix-sha-256-condition-type-condition}

The fingerprint of a PREFIX-SHA-256 condition is the SHA-256 digest of the fingerprint contents as defined below:

    PrefixSha256ConditionFingerprintContents ::= SEQUENCE {
      prefix OCTET STRING,
      subcondition Condition
    }

prefix
: is an arbitrary octet string which will be prepended to the message during validation.

subcondition
: is the sub-condition derived from the sub-fulfillment.

### MaxFulfillmentLength {#prefix-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the size, in bytes, of the prefix plus the maxFulfillmentLength of the sub-crypto-condition.

### Fulfillment Format {#prefix-sha-256-condition-type-fulfillment}

    PrefixSha256FulfillmentPayload ::= SEQUENCE {
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
THRESHOLD-SHA-256 is assigned the type ID 2. It relies on the availability of the SHA-256 digest algorithm and is a compound crypto-condition type.

### Condition Format {#threshold-sha-256-condition-type-condition}

The fingerprint of a THRESHOLD-SHA-256 condition is the SHA-256 digest of the fingerprint contents given below:

    ThresholdSha256FingerprintContents ::= SEQUENCE {
      threshold INTEGER (1..255),
      subconditions SEQUENCE OF Condition,
    }

The list of sub-conditions is sorted first based on length, shortest first. Elements of the same length are sorted in lexicographic (big-endian) order, smallest first.  

threshold
: threshold MUST be an integer in the range 1 ... 255. In order to fulfill a threshold condition, the number of valid sub-fulfillments MUST be greater than or equal to the threshold.

subconditions
: is the set of sub-conditions either provided in the fulfillment or derived from the sub-fulfillments provided.


### MaxFulfillmentLength {#threshold-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is sum of the maxFulfillmentLength of all sub-conditions and sub-fulfillments.

### Fulfillment Format {#threshold-sha-256-condition-type-fulfillment}

    ThresholdSha256FulfillmentPayload ::= SEQUENCE {
      threshold INTEGER (0..255),
      subfulfillments SEQUENCE OF Fulfillment
      subconditions SEQUENCE OF Condition
    }

threshold
: is a number and MUST be an integer in the range 1 ... 255. In order to fulfill a threshold condition, the sum of the provided fulfillments MUST be greater than or equal to the threshold.

subfulfillments
: is the set of sub-fulfillments.

subconditions
: is the set of sub-conditions provided in place of any unfufilled sub-fulfillment.

### Validating {#threshold-sha-256-condition-type-validating}

A THRESHOLD-SHA-256 fulfillment is valid iff :
 
  1. The number of valid F.subfulfillments is equal to or greater than F.threshold.
  2. D is equal to C. 

### Example {#threshold-sha-256-example}

TODO


## RSA-SHA-256 {#rsa-sha-256-condition-type}
RSA-SHA-256 is assigned the type ID 3. It relies on the SHA-256  digest algorithm and the RSA-PSS signature scheme.

The signature algorithm used is RSASSA-PSS as defined in PKCS#1 v2.2. [RFC3447](#RFC3447)  

Implementations MUST NOT use the default RSASSA-PSS-params. Implementations MUST use the SHA-256 hash algorithm and therefor, the same algorithm in the mask generation algorithm, as recommended in [RFC3447](#RFC3447). Implementations MUST also use a salt length of 32 bytes (equal to the size of the output from the SHA-256 algorithm). Therefore the algorithm identifier will have the following value:

    rSASSA-PSS-Crypto-Conditions-Identifier  RSASSA-AlgorithmIdentifier ::= {
        algorithm   id-RSASSA-PSS,
        parameters  RSASSA-PSS-params : {
            hashAlgorithm       sha256,
            maskGenAlgorithm    mgf1SHA256,
            saltLength          32,
            trailerField        trailerFieldBC
        }
    }
   
    sha256 HashAlgorithm ::= {
        algorithm   id-sha256,
        parameters  NULL
    }
    
    mgf1SHA256 MaskGenAlgorithm ::= {
        algorithm   id-mgf1,
        parameters  HashAlgorithm : sha256
    }

### Condition Format {#rsa-sha-256-condition-type-condition}
The fingerprint of a RSA-SHA-256 condition is the SHA-256 digest of the fingerprint contents given below:

    RsaSha256FingerprintContents ::= SEQUENCE {
      modulus OCTET STRING (SIZE(128..512))
    }


modulus
: is an octet string representing the RSA public modulus in big-endian byte order. The first byte of the modulus MUST NOT be zero.

: The corresponding public exponent e is assumed to be 65537 as recommended in [RFC4871](#RFC4871) . Very large exponents can be a DoS vector [LARGE-RSA-EXPONENTS](#LARGE-RSA-EXPONENTS) and 65537 is the largest Fermat prime, which has some nice properties [USING-RSA-EXPONENT-OF-65537](#USING-RSA-EXPONENT-OF-65537) .

: Implementations MUST reject moduli smaller than 128 bytes (1017 bits) or greater than 512 bytes (4096 bits.) Large moduli slow down signature verification which can be a denial-of-service vector. DNSSEC also limits the modulus to 4096 bits [RFC3110](#RFC3110) . OpenSSL supports up to 16384 bits [OPENSSL-X509-CERT-EXAMPLES](#OPENSSL-X509-CERT-EXAMPLES) .

### MaxFulfillmentLength {#rsa-sha-256-condition-type-maxfulfillmentlength}

The maxFulfillmentLength is the length in bytes of the modulus multiplied by 2.

### Fulfillment Format {#rsa-sha-256-condition-type-fulfillment}

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

### Validating {#rsa-sha-256-condition-type-validating}

An RSA-SHA-256 fulfillment is valid iff :
 
  1. F.signature is valid for the message M, given the RSA public key derived using a modulus of F.modulus and an exponent of 65537.
  2. D is equal to C. 

### Example {#rsa-sha-256-example}

TODO

## ED25519 {#ed25519-condition-type}
ED25519 is assigned the type ID 4. It relies on the SHA-512 digest algorithm and the ED25519 signature scheme as the condition fingerprint is not a digest.

The exact algorithm and encodings used for the public key and signature are defined in [I-D.irtf-cfrg-eddsa](#I-D.irtf-cfrg-eddsa) as Ed25519. SHA-512 is used as the hashing function.

### Condition Format {#ed25519-condition-type-condition}

The fingerprint of an ED25519 condition is the 32 byte Ed25519 public key. Since the public key is already very small, we do not hash it.

### Fulfillment {#ed25519-condition-type-fulfillment}

    Ed25519FulfillmentPayload ::= SEQUENCE {
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

TODO

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
        fingerprint OCTET STRING,
        maxFulfillmentLength INTEGER (0..MAX),
        subtypes OCTET STRING
    }

    Fulfillment ::= SEQUENCE {
        type ConditionType,
        payload OCTET STRING
    }

    ConditionType ::= INTEGER {
        preimageSha256(0),
        prefixSha256(1),
        thresholdSha256(2),
        rsaSha256(3),
        ed25519(4)
    } (0..255)
        
    /**
    * FULFILLMENT PAYLOADS
    */

    -- For preimage conditions, the payload equals the preimage

    PrefixSha256FulfillmentPayload ::= SEQUENCE {
        prefix OCTET STRING,
        subfulfillment Fulfillment
    }

    ThresholdSha256FulfillmentPayload ::= SEQUENCE {
        threshold INTEGER (1..255),
        subfulfillments SEQUENCE OF Fulfillment,
        subconditions SEQUENCE OF Condition
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
        threshold INTEGER (1..255),
        subconditions SEQUENCE OF Condition
    }

    RsaSha256FingerprintContents ::= SEQUENCE {
        modulus OCTET STRING (SIZE(128..512))
    }
    
    /**
    * EXAMPLES
    */

    exampleCondition Condition ::=
    {
        type preimageSha256,
        fingerprint '
        E3B0C442 98FC1C14 9AFBF4C8 996FB924 27AE41E4 649B934C A495991B 7852B855
        'H,
        maxFulfillmentLength 2,
        subtypes ''B
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

The following types are registered:

| Type ID | Type Name         |
|---------|-------------------|
| 0       | PREIMAGE-SHA-256  |
| 1       | PREFIX-SHA-256    |
| 2       | THRESHOLD-SHA-256 |
| 3       | RSA-SHA-256       |
| 4       | ED25519           |
{: #crypto-condition-types-table title="Crypto-Condition Types"}

# String Encoding {#appendix-f}

Implementations MAY support one or both string encoding formats which encode conditions and fulfillments as either URIs or JSON objects. The binary encoding is considered the canonical encoding.

The following string encoding types are defined:

BASE10
: Variable-length integer encoded as a base-10 (decimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows.

BASE16
: Variable-length integer encoded as a base-16 (hexadecimal) number. Implementations MUST reject encoded values that are too large for them to parse. Implementations MUST be tested for overflows. Encodings may have an odd number of characters as the encoding excludes leading zeros.

BASE64URL
: Base64-URL encoding. See [RFC4648](#RFC4648), Section 5.

## Condition URI Format {#string-condition-format}

Conditions are ASCII encoded as:

    "cc:" BASE10(type) ":" BASE64URL(fingerprint) ":" 
    BASE10(maxFulfillmentLength) ":" BASE16(subtypes) 

For simple types the subtypes field (and ":" prefix) may be excluded.

### Example Condition

An example condition:

    0x00000000 00 00 01 03 20 7F 83 B1 65 7F F1 FC 53 B9 2D C1 ........e...S.-.
    0x00000010 81 48 A1 D6 5D FC 2D 4B 1F A3 D6 77 28 4A DD D2 .H..].-K...w(J..
    0x00000020 00 12 6D 90 69 03 FF FF FF                      ..m.i....
    
    cc:0:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66

The example has the following attributes:

| Field                | Value | Description |
|----------------------|-------|----------------------------------------------|
| preface              | `cc`  | Constant. Indicates this is a condition. |
| type                 | `0`   | Type 0 is [PREIMAGE-SHA-256][]. |
| fingerprint          | `dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA` | The hash of the fulfillment for this condition. |
| maxFulfillmentLength | `66`  | The fulfillment payload is 66 bytes long, before being BASE64URL-encoded. |
| subtypes             | ``    | Absent |

### Fulfillment URI Format {#string-fulfillment-format}

Fulfillments are ASCII encoded as:

    "cf:" BASE10(type) ":" BASE64URL(payload)

### Example Fulfillment

The following is an example fulfillment in string format, for the [example condition](#example-condition):

    cf:0:VGhlIG9ubHkgYmFzaXMgZm9yIGdvb2QgU29jaWV0eSBpcyB1bmxpbWl0ZWQgY3JlZGl0LuKAlE9zY2FyIFdpbGRl

The example has the following attributes:

| Field                | Value | Description |
|----------------------|-------|----------------------------------------------|
| preface              | `cf`  | Constant. Indicates this is a fulfillment. |
| type                 | `0`   | Type 0 is [PREIMAGE-SHA-256][]. |
| payload              | `VGhlIG...pbGRl` | The BASE64URL-encoded SHA-256 preimage of the condition, since this is a PREIMAGE-SHA-256 type fulfillment. In this case, it is an arbitrary string. |

