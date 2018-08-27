---
title: Pre-Shared Key V2 (PSKv2) Transport Protocol
draft: FINAL
deprecated: 0029-stream
---
# Pre-Shared Key V2 (PSKv2) Transport Protocol

Version 2 of the Pre-Shared Key Transport Protocol is a request/response protocol built on ILP that handles condition generation and data encryption and authentication. It can be used for individual payments or messages, [end-to-end quoting](#end-to-end-quoting), and as a building block for streaming and chunked payments use cases.

**Table of Contents**

* [Overview](#overview)
  + [Relation to Other Protocols](#relation-to-other-protocols)
  + [Setup](#setup)
  + [Encryption](#encryption)
  + [Conditions and Fulfillments](#conditions-and-fulfillments)
  + [End-To-End Quoting](#end-to-end-quoting)
* [Model of Operation](#model-of-operation)
  + [Informational Quote](#informational-quote)
  + [Single Payment](#single-payment)
* [Specification](#specification)
  + [Encryption](#encryption-1)
  + [Data Packet](#data-packet)
  + [Condition and Fulfillment Generation](#condition-and-fulfillment-generation)

## Overview

Like [PSKv1](./0016-pre-shared-key/0016-pre-shared-key.md), PSKv2 uses a secret shared between the sender and receiver to generate the conditions and fulfillments for payments without the need for repeated end-to-end communication. PSKv2 can be used to send individual packets or multiple, as well as unfulfillable test payments that may be used for quotes.

### Relation to Other Protocols

PSKv2 is designed to work with ILPv4 Prepare, Fulfill, and Reject packets.

PSKv2 may be used by applications or higher-level protocols for sending individual requests and responses or for informational quotes.

PSKv2 does not include features for segmenting and reassembling packets for Chunked Payments, but it may be used in higher-level protocols that implement such functionality. Those higher-level protocols may include additional fields in the data field of the PSK packets to group or order individual requests and responses.

### Setup

Before using PSKv2, the sender and receiver use an authenticated, encrypted communication channel (generally provided as part of an [Application Layer Protocol](./0001-interledger-architecture/0001-interledger-architecture.md#application-layer)) to exchange:

- PSK version (such as `2.0` for this version)
- A 32-byte random or pseudorandom shared secret
- The receiver's ILP address

The receiver MAY generate the shared secret from a longer-term secret and a nonce, as described in [PSKv1's Appendix A: Recommended Algorithm for Generating Shared Secrets](./0016-pre-shared-key/0016-pre-shared-key.md#appendix-a-recommended-algorithm-for-generating-shared-secrets). In this case, the receiver would append the nonce (**not** the secret) to their ILP address to create the destination address they communicate to the sender.

### Encryption

In PSKv2.0, request and response data is encrypted using [AES-256-GCM](https://en.wikipedia.org/wiki/Galois/Counter_Mode) with a 12-byte Initialization Vector (IV) and a 16-Byte Authentication Tag.

If subsequent versions support additional encryption algorithms, those details should be exchanged between the sender and receiver when they establish the pre-shared key. If a receiver attempts to decrypt an incoming packet but is unable to (perhaps because the sender is using an unsupported cipher), they SHOULD reject the incoming transfer with an `F06: Unexpected Payment` error.

### Conditions and Fulfillments

The sender and receiver generate the condition and fulfillment using the pre-shared key that gives this protocol its name. The fulfillment is computed from the pre-shared key and the encrypted PSK data. The condition is the hash of the fulfillment.

As in PSKv1, this method for generating the condition and fulfillment enables many payments to be sent without end-to-end communication for each one. However, because the sender also knows the fulfillment up-front, neither version of PSK allows the sender to use the fulfillment as a non-repudiable proof of payment. For use cases where this is desired, a Transport Protocol like the [Interledger Payment Request (IPR)](./0011-interledger-payment-request/0011-interledger-payment-request.md) should be used instead.

### End-To-End Quoting

In contrast to PSKv1, which depends on the [Interledger Quoting Protocol (ILQP)](./0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md), PSKv2 has two built-in mechanisms for discovering the exchange rate of a given path: informational quotes and dynamic price discovery.

For purely informational quotes, PSKv2 uses unfulfillable test payments to the receiver to determine the exchange rate for a given path. The condition is set to a random 32-byte condition (with no known fulfillment). When the receiver gets the incoming payment, they reject the incoming transfer and include in their response how much arrived in that transfer. The sender can use the source amount they set and the receiver's response to determine the rate.

When a sender is sending many payments to the receiver, they need a dynamic view of the exchange rate because the rate may change during the course of the interaction. To handle these cases, every PSKv2 payment response includes the amount that arrived in the final transfer to the receiver. Similar to the informational quotes, the sender can use the packet's source amount and the receiver's response to determine and monitor the exchange rate.

**Judging Prices by Source Units:** With any type of Interledger quoting, whether end-to-end or using ILQP, senders SHOULD judge prices in their source units. Receivers can lie about how much arrives in a test payment for a quote or they could run their own ledger and connector that happen to have a bad exchange rate. Therefore, senders must assume that whatever amount the receiver says has arrived represents the "real" rate of the path.

**Linear Exchange Rates and Fixed Destination Amount Quotes:** End-to-End Quoting works best with linear exchange rates. If the rate for a path is linear, it can be determined by sending a single test payment for an arbitrary amount. The source amount required to deliver a fixed destination amount can be easily determined by dividing the source amount by the rate. If exchange rates are non-linear, getting an informational quote for a fixed destination amount would require a binary search, which is not ideal. However, in an Interledger network primarily or exclusively suited to small payments, there should be little reason for rates to vary by payment size.

## Model of Operation

### Informational Quote

1. Sender creates a packet with a type of 4, a random Request ID, and the Request Amount set to 2^64 - 1 (the maximum unsigned 64-bit integer, or 18446744073709551615). Sender [encrypts](#encryption-envelope) the packet using the encryption key derived using the method described in [Encryption Pseudocode](#encryption-pseudocode).
2. Sender generates a random 32-byte condition.
3. Sender sends an ILP Prepare packet with the condition, encrypted data and either the chosen source amount (in the case of a fixed source amount payment) or an arbitrary amount (in the case of a fixed destination amount).
4. Receiver is notified of the incoming Prepare packet, rederives the encryption key as described in [Encryption Pseudocode](#encryption-pseudocode), and decrypts the PSK Request.
5. Receiver compares the Request Amount from the Request with the amount in the Prepare packet they received. They note that the incoming transfer amount is too low.
6. Receiver creates a PSK Error packet, using the same Request ID from the sender's Request and setting the Request Amount to the amount that arrived in the Prepare packet. Receiver [encrypts](#encryption-envelope) the packet using the same encryption key as before.
7. Receiver replies to the ILP Prepare packet with an ILP Reject that includes the encrypted PSK Error packet in the Reject's data field.
8. Sender gets the ILP Reject packet, decrypts the PSK Error and divides the receiver's Request Amount by the amount the sender sent in the original ILP Prepare packet to determine the approximate path exchange rate.

### Single Payment

1. Sender determines the source amount and minimum destination amounts for the packet, potentially using the exchange rate as determined by an [Informational Quote](#informational-quote) or from sending previous requests.
2. Sender creates a PSK Request with a random Request ID and the Request Amount set to the destination amount determined in step 1. Sender MAY include additional data in the PSK Request. Sender derives the encryption key as described in [Encryption Pseudocode](#encryption-pseudocode) and [encrypts](#encryption-envelope) the Request.
3. Sender generates a condition as described in [Fulfillable Condition](#fulfillable-condition).
4. Sender sends an ILP Prepare using the source amount determined in step 1, the condition from step 3, and the encrypted Request from step 2 as the data.
5. Receiver is notified of the incoming ILP Prepare packet, rederives the encryption key as described in [Encryption Pseudocode](#encryption-pseudocode), and decrypts the data. (The receiver SHOULD return an ILP Reject with the code `F06: Unexpected Payment` if they are unable to decrypt the data)
6. Receiver checks to ensure that the amount in the ILP Prepare packet is greater than or equal to the Request Amount specified in the PSK Request. The receiver SHOULD return an ILP Reject packet with the code `F99: Application Error` and an encrypted PSK Error packet, which includes the amount that arrived in the prepare, as the data.
7. Receiver creates a PSK Response with the same Request ID and the Request Amount set to the amount that arrived in the ILP Prepare packet. The receiver then [encrypts](#encryption-envelope) the data using the same encryption key.
8. Receiver generates fulfillment as described [below](#fulfillment-generation) and fulfills the incoming transfer with the fulfillment and the encrypted response data. The receiver SHOULD return an ILP Reject with an `F05: Wrong Condition` code if they are unable to regenerate the correct condition.
9. Sender gets the ILP Fulfill packet and decrypts the PSK Response from the data. They SHOULD ignore the Response if the Request ID does not match their original request or if the PSK packet is not a Response type. They may use the Request Amount from the Response to estimate the path exchange rate. They may also use the data in the PSK Response from the receiver.

## Specification

### Encryption

Request and response data are encrypted using [AES-256-GCM](https://en.wikipedia.org/wiki/Galois/Counter_Mode) with a random 12-byte Initialization Vector (IV) and a 16-byte Authentication Tag.

#### Encryption Envelope

Also see the [ASN.1 definition](../asn1/PreSharedKeyV2.asn).

```
(Numbers represent bytes)

       4       8       12      16      20      24      28      32
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|       Random IV       |       Authentication Tag      | Ciph..|
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          Ciphertext                           |
\                                                               \
\                                                               \
|                          Ciphertext                           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

| Field | Type | Description |
|---|---|---|
| Random IV  | 12-Byte UInt | Nonce used as input to the AES-GCM algorithm. Also ensures conditions are random. Senders MUST NOT encrypt two packets with the same nonce |
| Authentication Tag   | 16-Byte UInt | Authentication tag produced by AES-GCM encryption that ensures data integrity |
| Ciphertext | 0-32739 Bytes | Encrypted data (see below for contents) |

#### Encryption Pseudocode

Note that the encryption key is derived from the shared secret using an HMAC.

```
iv = random_bytes(12)
encryption_key = hmac_sha256(shared_secret, "ilp_psk_encryption")
{ ciphertext, auth_tag } = aes_256_gcm(encryption_key, iv, data)
```

### Data Packet

All PSKv2.0 requests and responses encode their data in the same byte format, though the meanings of the fields differ depending on whether it is a request or a response.

The following is encrypted, as defined [above](#encryption), and set as the data in an ILP Prepare, Fulfill, or Reject packet.

Also see the [ASN.1 definition](../asn1/PreSharedKeyV2.asn).

```
(Numbers represent bytes)

       4       8       12      16      20      24      28      32
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|T| ReqID | Request Amount|         Application Data            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Application Data                        |
\                                                               \
\                                                               \
|                       Application Data                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          Junk Data                            |
\                                                               \
\                                                               \
|                          Junk Data                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

#### Request

PSK Request packets should ONLY be sent in ILP Prepare packets.

| Field | Type | Description |
|---|---|---|
| Type (T) | Always `4` (UInt8) | Indicates that this is a PSK2 request. Request packets SHOULD be rejected or ignored if they are not in an ILP Prepare packet. |
| Request ID (ReqID) | UInt32 | ID used to correlate requests and responses. Senders CANNOT rely on receivers enforcing uniqueness, but they SHOULD ensure that responses carry the same Request ID as the outgoing request |
| Request Amount | UInt64 | Minimum amount that should arrive in the ILP Prepare packet for the receiver to fulfill it. Receivers SHOULD NOT accept packets where the Request Amount is greater than the ILP Prepare amount |
| Data | [OER Variable-Length Octet String](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) | User data carried along with the payment. Note this data is encrypted and authenticated |
| Junk Data | 0-? Bytes | _(Optional)_ Extra data included to obscure what the ILP payment is for. Receivers SHOULD ignore this data. Later versions of this protocol MAY define additional fields that will be added after the `data` field and older implementations will simply disregard those. |

#### Response

PSK Response packets should ONLY be sent in ILP Fulfill packets.

| Field | Type | Description |
|---|---|---|
| Type (T) | Always `5` (UInt8) | Indicates that this is a PSK2 response. Response packets SHOULD be rejected or ignored if they are not in an ILP Fulfill packet. |
| Request ID (ReqID) | UInt32 | ID used to correlate requests and responses. Receivers MUST use the same Request ID from the Request in their Response. Senders SHOULD ignore responses whose Request ID does not match their original request. |
| Request Amount | UInt64 | Amount that arrived in the ILP Prepare packet the receiver got. This is used to help senders determine the path exchange rate and how much the receiver has gotten. Note the sender must trust the receiver to report this honestly. |
| Data | [OER Variable-Length Octet String](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) | User data carried along with the payment. Note this data is encrypted and authenticated |
| Junk Data | 0-? Bytes | _(Optional)_ Extra data included to obscure what the ILP payment is for. Receivers SHOULD ignore this data. Later versions of this protocol MAY define additional fields that will be added after the `data` field and older implementations will simply disregard those. |

#### Error

PSK Response packets should ONLY be sent in ILP Reject packets.

| Field | Type | Description |
|---|---|---|
| Type (T) | Always `6` (UInt8) | Indicates that this is a PSK2 error. Response packets SHOULD be rejected or ignored if they are not in an ILP Reject packet. |
| Request ID (ReqID) | UInt32 | ID used to correlate requests and responses. Receivers MUST use the same Request ID from the Request in the Error. Senders SHOULD ignore responses whose Request ID does not match their original request. |
| Request Amount | UInt64 | Amount that arrived in the ILP Prepare packet the receiver got. This is used to help senders determine the path exchange rate and how much the receiver has gotten. Note the sender must trust the receiver to report this honestly. |
| Data | [OER Variable-Length Octet String](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) | User data carried along with the payment. Note this data is encrypted and authenticated |
| Junk Data | 0-? Bytes | _(Optional)_ Extra data included to obscure what the ILP payment is for. Receivers SHOULD ignore this data. Later versions of this protocol MAY define additional fields that will be added after the `data` field and older implementations will simply disregard those. |


### Condition and Fulfillment Generation

There are two methods the sender can use to generate the condition, depending on whether they want the payment to be fulfillable or not.

#### Unfulfillable Condition

If the sender does not want the receiver to be able to fulfill the payment (as for an informational quote), they can generate an unfulfillable random condition.

```
condition = random_bytes(32)
```

#### Fulfillable Condition

If the sender does want the receiver to be able to fulfill the condition, the condition MUST be generated in the following manner.

The `shared_secret` is the pre-shared key that gives this protocol its name. The `data` is the **encrypted** PSK Request.

```
hmac_key = hmac_sha256(shared_secret, "ilp_psk2_fulfillment")
fulfillment = hmac_sha256(hmac_key, data)
condition = sha256(fulfillment)
```

#### Fulfillment Generation

The following pseudocode details how the receiver regenerates the fulfillment from the data.

**Note:** Senders MAY use unfulfillable conditions to get an informational quote. Receivers MUST return an [Error Response](#error) packet that includes the amount that arrived on the incoming transfer, even if they are unable to regenerate the fulfillment from the request.

The `shared_secret` is the pre-shared key that gives this protocol its name. The `data` is the **encrypted** PSK Request.

```
hmac_key = hmac_sha256(shared_secret, "ilp_psk2_fulfillment")
fulfillment = hmac_sha256(hmac_key, data)
```

