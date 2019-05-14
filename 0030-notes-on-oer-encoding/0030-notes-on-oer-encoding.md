---
title: Notes on OER Encoding
draft: 3
---

# Introduction

The Interledger stack consists of a collection of different protocols. In order to keep some consistency between these separate, but related protocols, the Interledger team has decided to use some common choices for encoding formats across at least those protocols we control.

These choices will not be applicable for all protocols in the Interledger ecosystem. For example, we used a binary encoding while a text-based encoding may be more suitable. We used an encoding with a fixed schema, while a schema-less encoding may be easier to extend by third-parties.

Nevertheless, designers of new Interledger protocols SHOULD consider staying within the boundaries set by this document. Deviations from these norms should be carefully considered. This is intended to minimize the load on implementors who should be able to write components such as date encoding and decoding once and reuse it across protocols.

# How to use this document

This document is intended as a first reference for implementors to use when writing code that serializes and deserializes Interledger formats. We intend to make this document sufficient on its own, such that reading the official ASN.1/OER specifications is not required to correctly implement Interledger formats.

Implementors SHOULD NOT aim to create a full-featured OER parser, since Interledger intentionally does not use some of the more complex features of ASN.1. Implementors MAY use a full-featured CANONICAL-OER implementation, but we expect most will prefer a lighter-weight implementation that only handles types that are actually used in the Interledger protocols.

# Foundation

Interledger encodings are based on and compliant with Abstract Syntax Notation One (ASN.1) using Canonical Octet Encoding Rules (CANONICAL-OER).

## ASN.1

### What is ASN.1?

Abstract Syntax Notation One (ASN.1) is an international standard for describing abstract data types. ITU gives the following definition:

> Abstract Syntax Notation number One
> is a standard that defines a formalism
> for the specification of abstract data types.

In plain English, ASN.1 describes what your data can be, without making any statements about how it could be encoded in bits and bytes.

### Why ASN.1?

A protocol like Interledger is fundamentally a set of guidelines for a conversation between different computers. The more precise this set of guidelines is, the less likely it is that there will be a misunderstanding. It is the job of the protocol designer to specify this conversation with as little ambiguity as possible.

Using a formalized language like ASN.1 to describe one's protocol means that one can use automated tools to verify the consistency and completeness of one's specification. This is a very valuable tool. It also means that one can refer to existing specifications which already cover many edge cases. Otherwise, each protocol would have to answer all possible edge cases itself, which quickly becomes tedious.

ASN.1 is by far the most widely used formalized language for defining protocols. As an ISO and ITU standard, it is used in telecommunications protocols, cryptography standards and many more.

The Interledger team chose ASN.1 because of it's long history and robust ecosystem. It may not be the most modern of standards, but it is extremely powerful and comes with huge amounts of implementation experience. Also, there exist high-quality tools for protocol designers.

## CANONICAL-OER

### What is OER/CANONICAL-OER?

The Octet Encoding Rules (OER) are a set of simple byte-aligned encoding rules for ASN.1 types.

CANONICAL-OER narrows BASIC-OER to a single canonical encoding.

### Why CANONICAL-OER?

For Interledger, we wanted to use the power of ASN.1 in order to design and validate our protocols and to avoid any ambiguity for implementors. However, we also wanted it to be easy to implement Interledger encodings, without having to first learn a bunch of ASN.1 and related technology. OER gives us the best of both worlds, because its encodings are extremely simple and can easily be described and implemented without referencing ASN.1 or OER. Yet, we can use standard tools to generate test data and validate our implementations. And we can refer to the ASN.1/OER specs to resolve any ambiguities that are discovered later.

OER is designed to strike a better compromise between simplicity, speed and size than previous ASN.1 encoding rules. All OER types are byte-aligned, which makes them easier to serialize and parse in most programming languages than Packed Encoding Rules (PER) and also faster on most platforms.

We chose CANONICAL-OER instead of BASIC-OER because we wanted a canonical encoding format so that Interledger encodings could be used for cryptographic operations like hashing and signing.

## Basics

### Octet strings

All Interledger formats are byte-aligned messages and should be passed as octet strings, i.e. sequences of bytes. The correct type for this would be a `Buffer` in JavaScript, `byte[]` in Java, `bytes` in Python, etc.

### Extensibility

For most Interledger formats, we require that implementations MUST ignore extra bytes at the end of the message. This behavior allows additional fields to be added in the future that are automatically ignored by existing implementations.

## Types

### Fixed-length unsigned integers

> Used in: ILP, BTP

All fixed-length unsigned integers are encoded in big-endian, least-significant bit last. Interledger encoding provides the following fixed-length unsigned integers:

| Type | Size | Range |
| :--- | :--- | :--- |
| UInt8 | 1 byte | 0 .. 255 (2^8 - 1) |
| UInt16 | 2 bytes | 0 .. 65535 (2^16 - 1) |
| UInt32 | 4 bytes | 0 .. 4294967295 (2^32 - 1) |
| UInt64 | 8 bytes | 0 .. 18446744073709551615 (2^64 - 1) |
| UInt128 | 16 bytes | 0 .. 2^128 - 1 |
| UInt160 | 20 bytes | 0 .. 2^160 - 1 |
| UInt192 | 24 bytes | 0 .. 2^192 - 1 |
| UInt224 | 28 bytes | 0 .. 2^224 - 1 |
| UInt256 | 32 bytes | 0 .. 2^256 - 1 |
| UInt384 | 48 bytes | 0 .. 2^384 - 1 |
| UInt512 | 64 bytes | 0 .. 2^512 - 1 |

For UInt64 and smaller, implementations SHOULD use internal methods that can serialize/deserialize any unsigned integer of size 1-8 bytes. This can also be used to decode the [length determinant](#length-determinant).

Unsigned integers larger than 8 bytes MAY be represented as a byte string.

#### Examples

| Type | Bytes | Decoded value |
| :--- | :--- | :--- |
| UInt8 | `00` | `0` |
| UInt16 | `1234` | `4660` |
| UInt32 | `ABABABAB` | `2880154539` |
| UInt64 | `AC01055A 1DEBAC1E` | `12394193534107495454` |
| UInt256 | `FF713A73 8B32F2D3 29898CD9 7A42D75A`<br>`86D9E59E B3928E7B 7BFAADF4 A4689459` | `byte[32]` |
| UInt512 | `37DA42AC 9C322C80 E5D7FD75 112CBEAD`<br>`B0B9FD10 E27A68FE 2DA16BE9 DB0BC10D`<br>`76EC90B0 BB136B13 EF033692 53119203`<br>`21B47236 C42FB4D1 A4DC52B6 DD0556E2` | `byte[64]` |

### Fixed-length signed integers

> Not currently used

All fixed-length signed integers are encoded in big-endian, least-significant bit last. Negative values are encoded using 2's complement binary encoding.

| Type | Size | Range |
| :--- | :--- | :--- |
| Int8 | 1 byte | -128 .. 127 |
| Int16 | 2 bytes | -32768 .. 32767 |
| Int32 | 4 bytes | -2147483648 .. 2147483647 |
| Int64 | 8 bytes | -9223372036854775808 .. 9223372036854775807 |

#### Examples

| Type | Bytes | Decoded value |
| :--- | :--- | :--- |
| Int8 | `00` | `0` |
| Int8 | `7F` | `127` |
| Int8 | `FF` | `-1` |
| Int8 | `80` | `-128` |
| Int16 | `0000` | `0` |
| Int16 | `7FFF` | `32767` |
| Int16 | `FFFF` | `-1` |
| Int16 | `8000` | `-32768` |
| Int16 | `FC00` | `-1024` |
| Int16 | `CFC7` | `-12345` |
| Int32 | `00000000` | `0` |
| Int32 | `7FFFFFFF` | `2147483647` |
| Int32 | `FFFFFFFF` | `-1` |
| Int32 | `80000000` | `-2147483648` |
| Int32 | `0C00F5C9` | `201389513` |
| Int32 | `F204BA10` | `-234571248` |
| Int64 | `00000000 00000000` | `0` |
| Int64 | `7FFFFFFF FFFFFFFF` | `9223372036854775807` |
| Int64 | `FFFFFFFF FFFFFFFF` | `-1` |
| Int64 | `80000000 00000000` | `-9223372036854775808` |
| Int64 | `0C1B3391 3EFE4F1F` | `872347651746451231` | 
| Int64 | `EF68FE12 0BC51AD7` | `-1195426347606533417` |
| Int64 | `909701ED F43AE528` | `-8027945689248242392` |

### Fixed-length floating point numbers

> Not currently used

Floating point values in Interledger are encoded using IEEE 754 binary floating point.

| Type | Size | IEEE 754 name |
| :--- | :--- | :--- |
| Float32 | 4 bytes | binary32 |
| Float64 | 8 bytes | binary64 |

#### Examples

| Type | Bytes | Decoded value |
| :--- | :--- | :--- |
| Float32 | `3F8FCD36` | `1.12345` (approximately) |
| Float64 | `3FF1F9A6B50B0F28` | `1.12345` (approximately) |

### Fixed-length octet string

> Used in: ILP, BTP

A fixed length octet string is encoded as itself with no added prefix or suffix.

### Length determinant

> Used in: ILP, BTP

All variable-length fields are prefixed with a length determinant. The length determinant can be either short form or long form.

#### Short form

A single byte in the range 0 .. 127, denoting the length.

#### Long form

A single byte in the range 128 .. 255, denoting the value *128 + n*, where *n* is the length-of-length. This is followed by an unsigned integer of *n* bytes denoting the length. This length MUST NOT contain leading zeros. If the length is less than 127, the short form encoding MUST be used.

Implementations MAY limit the length determinants they support to a length-of-length of no more than eight bytes. Interledger protocols MUST NOT use length determinants greater than `18446744073709551615 (2^64 - 1)`.

#### Examples

| Encoding | Decoded value |
| :--- | :--- |
| `07` | `7` |
| `8182` | `130` |
| `821234` | `4660` |
| `83ABCDEF` | `11259375` |
| `88AC0105 5A1DEBAC 1E` | `12394193534107495454` |

### Variable-length octet string

> Used in: ILP, BTP

A variable length octet string consists of a length determinant, followed by that many bytes.

### Variable-length unsigned integer

> Not currently used

A variable length unsigned integer consists of a length determinant, followed by a big-endian integer of that many bytes. Leading zeros MUST NOT be used.

### Variable-length signed integer

> Not currently used

A variable length signed integer consists of a length determinant, followed by a 2's complement bin-endian integer of that many bytes. The first byte MAY be zero if and only if the first bit of the second byte is set. Otherwise, leading zeros MUST NOT be used.

### Variable-length string

> Used in: ILP, BTP

A variable length string consists of a length determinant, followed by that many bytes. UTF-8 MUST be used as the character encoding unless otherwise specified.

### Fixed-length Timestamps

> Used in: ILP

ILP Timestamps are encoded using ASN.1 PrintableString with a fixed length of 17, using a shortened and slightly restricted variant of ISO-8601 encoding.

#### Encoding

When encoding an ISO-8601 ILP timestamp, the hyphens, colons, `T` character, decimal period, and any `Z` timezone indicator MUST be removed. The date MUST denote UTC time, as local timezones are not allowed. Years MUST be given as four digits and MUST NOT be left out. Months, day, hours, minutes and seconds MUST be given 
as two digits and MUST NOT be left out. Milliseconds MUST be given as three digits, and MUST NOT be left out. Midnight MUST be encoded as `000000000` on the following day. 
Leap seconds MUST be smeared across the entirety of a day according to [UTC-SLS](https://www.cl.cam.ac.uk/~mgk25/time/utc-sls/) (note that many programming languages support this functionality by default, including Java and Javascript. See [IL-RFC-481](https://github.com/interledger/rfcs/issues/481) for more details).

Here is how to encode certain dates:

* `2017-12-24T16:14:32.279112Z` ->  `20171224161432279` (rounded)
* `2017-12-24T16:14:32.279Z` ->     `20171224161432279`
* `2016-12-31T23.59.60.852Z` ->     `20161231235960852` (leap second)
* `2017-12-24T16:14:32.200Z` ->     `20171224161432200`
* `2017-12-24T16:14:32.000Z` ->     `20171224161432000`
* `2017-12-24T16:14:30.000Z` ->     `20171224161430000`
* `2017-12-24T16:14:00.000Z` ->     `20171224161400000`
* `2017-12-24T16:10:00.000Z` ->     `20171224161000000`
* `2017-12-24T16:00:00.000Z` ->     `20171224160000000`
* `2017-12-24T10:00:00.000Z` ->     `20171224100000000`
* `2017-12-24T00:00:00.000Z` ->     `20171224000000000`
* `2017-12-24T24:00:00.000Z` ->     `20171225000000000` (use correct midnight format)
* `2017-12-24T16:14:32,182Z` ->     `20171224161432182`
* `2017-12-24T18:14:32.000+0200` -> `20171224161432000` (converted to UTC)

#### Decoding

All required fields MUST be present. Extra elements MUST NOT be present. Midnight MUST be represented as `000000`. Leap seconds MUST be smeared across the entirety of a day according to [UTC-SLS](https://www.cl.cam.ac.uk/~mgk25/time/utc-sls/) (note that many programming languages support this functionality by default, including Java and Javascript. See [IL-RFC-481](https://github.com/interledger/rfcs/issues/481) for more details).  

The following examples are invalid and parsers MUST reject them:

* `20171224235312.431+0200` -> INVALID; not UTC, invalid characters
* `201712242153124318` -> INVALID; too much precision, invalid characters
* `20171324161432200` -> INVALID, month out of range
* `20171224230000000.` -> INVALID, spurious decimal point
* `20171224240000000` -> INVALID, wrong representation of midnight
* `20171224215300` -> INVALID, missing milliseconds
* `2017122421531` -> INVALID, missing digit in seconds and milliseconds
* `201712242153` -> INVALID, missing seconds and milliseconds
* `2017122421` -> INVALID, missing seconds, minutes, and milliseconds
* `20161231235960852` -> INVALID, unsmeared leap-second.

The following examples are valid and parsers MUST correct deserialize them:

* `20171224161432279` -> `2017-12-24T16:14:32.279Z`
* `20171224161432270` -> `2017-12-24T16:14:32.270Z`
* `20171224161432200` -> `2017-12-24T16:14:32.200Z`
* `20171224161432000` -> `2017-12-24T16:14:32.000Z`
* `20161231235959852` -> `2016-12-31T23:59:60.852Z` (nearly a leap second)
* `20171225000000000` -> `2017-12-25T00:00:00.000Z` (correct representation of midnight)
* `99991224161432279` -> `9999-12-24T16:14:32.279Z` (year 9999 is valid)

#### Examples

When encoded in binary, the shortened date string is encoded as a [fixed-length string](#fixed-length-string).

| Encoding | Decoded value |
| :--- | :--- |
| `32303137 31323234 31363134 33323237 39` | `20171224161432279` |
| `32303137 31323234 31363134 33323230 30` | `20171224161432200` |
| `32303137 31323235 30303030 30303030 30` | `20171225000000000` |

### Variable-length Timestamps

> Used in: BTP

Timestamps are encoded using ASN.1 GeneralizedTime. This is a shortened and slightly restricted variant of ISO 8601 encoding. Once the date string is derived it is encoded as a variable-length string.

#### Encoding

When encoding an ISO 8601 timestamp, the hyphens, colons and `T` character MUST be removed. The date MUST end in `Z`, denoting UTC time, local timezones are not allowed. Timestamps MAY use up to millisecond precision. The period `.` MUST be used as the decimal separator. If the millisecond part is zero, it MUST be left out. Trailing zeros in the millisecond part MUST be left out. Years MUST be given as four digits and MUST NOT be left out. Months, day, hours, minutes and seconds MUST be given as two digits and MUST NOT be left out. Midnight MUST be encoded as `000000` on the following day. Leap seconds MUST be encoded using `60` as the value for seconds.

Here is how to encode certain dates:

* `2017-12-24T16:14:32.279112Z` -> `20171224161432.279Z` (rounded)
* `2017-12-24T16:14:32.279Z` -> `20171224161432.279Z`
* `2016-12-31T23.59.60.852Z` -> `20161231235960.852Z` (leap second)
* `2017-12-24T16:14:32.200Z` -> `20171224161432.2Z`
* `2017-12-24T16:14:32.000Z` -> `20171224161432Z`
* `2017-12-24T16:14:30.000Z` -> `20171224161430Z`
* `2017-12-24T16:14:00.000Z` -> `20171224161400Z`
* `2017-12-24T16:10:00.000Z` -> `20171224161000Z`
* `2017-12-24T16:00:00.000Z` -> `20171224160000Z`
* `2017-12-24T10:00:00.000Z` -> `20171224100000Z`
* `2017-12-24T00:00:00.000Z` -> `20171224000000Z`
* `2017-12-24T24:00:00.000Z` -> `20171225000000Z` (use correct midnight format)
* `2017-12-24T16:14:32,182Z` -> `20171224161432.182Z` (use correct decimal separator)
* `2017-12-24T18:14:32.000+0200` -> `20171224161432Z` (converted to UTC)

#### Decoding

All required fields MUST be present. Extra elements MUST NOT be present. Midnight MUST be represented as `000000`. Implementations MUST allow leap seconds.

The following examples are invalid and parsers MUST reject them:

* `20171224235312.431+0200` -> INVALID, not UTC
* `20171224215312.4318Z` -> INVALID, too much precision
* `20171224161432,279Z` -> INVALID, wrong decimal element
* `20171324161432.279Z` -> INVALID, month out of range
* `20171224230000.20Z` -> INVALID, spurious trailing zero
* `20171224230000.Z` -> INVALID, spurious decimal point
* `20171224240000Z` -> INVALID, wrong representation of midnight
* `2017122421531Z` -> INVALID, missing digit in seconds
* `201712242153Z` -> INVALID, missing seconds
* `2017122421Z` -> INVALID, missing seconds and minutes

The following examples are valid and parsers MUST correct deserialize them:

* `20171224161432.279Z` -> `2017-12-24T16:14:32.279Z`
* `20171224161432.27Z` -> `2017-12-24T16:14:32.270Z`
* `20171224161432.2Z` -> `2017-12-24T16:14:32.200Z`
* `20171224161432Z` -> `2017-12-24T16:14:32.000Z`
* `20161231235960.852Z` -> `2016-12-31T23:59:60.852Z` (leap second)
* `20171225000000Z` -> `2017-12-25T00:00:00.000Z` (correct representation of midnight)
* `99991224161432.279Z` -> `9999-12-24T16:14:32.279Z` (year 9999 is valid)

#### Examples

When encoded in binary, the shortened date string is encoded as a [variable-length string](#variable-length-string).

| Encoding | Decoded value |
| :--- | :--- |
| `13323031 37313232 34313631 3433322E 3237395A` | `2017-12-24T16:14:32.279Z` |
| `11323031 37313232 34313631 3433322E 325A` | `2017-12-24T16:14:32.200Z` |
| `0F323031 37313232 35303030 3030305A` | `2017-12-25T00:00:00.000Z` |

### ILP Address

> Used in: ILP

ILP addresses MUST have a length in the range 0 .. 1023 and may contain uppercase `A-Z`, lowercase `a-z`, numbers `0-9`, hyphens `-`, underscores `_`, tildes `~` and periods `.`.

| Encoding | Decoded value |
| :--- | :--- |
| `18657861 6D706C65 2E746F70 2E6D6964 646C652E 6C6F7765 72` | `example.top.middle.lower` |
| `81826578 616D706C 652E7665 72792E6C 6F6E672E 61646472 6573732E 746F2E65 78636565 642E3132 372E6368 61726163 74657273 2E616E64 2E747269 67676572 2E612E6C 6F6E672E 666F726D 2E6C656E 6774682E 64657465 726D696E 616E742E 746F2E73 686F772E 686F772E 74686174 2E776F72 6B732E67 72656174 2E61732E 77656C6C` | `example.very.long.address.to.exceed.127.` `characters.and.trigger.a.long.form.` `length.determinant.to.show.how.that.` `works.great.as.well`<br><br>(newlines added for readability) |
