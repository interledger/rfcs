---
title: Pre-Shared Key V2 (PSKv2) Transport Protocol
draft: 1
---
# Pre-Shared Key V2 (PSKv2) Transport Protocol

This spec defines version 2 of the Pre-Shared Key Transport Protocol. PSKv2 is intended to be used for micropayments and larger [Chunked Payments](#chunked-payments). It includes end-to-end data encryption, condition and fulfillment generation, [End-to-End Quoting](#end-to-end-quoting) and an approach to Chunked Payments inspired by the Internet's Transmission Control Protocol (TCP).

**Table of Contents**

* [Overview](#overview)
  + [Setup](#setup)
  + [Encryption](#encryption)
  + [Condition and Fulfillment Generation](#condition-and-fulfillment-generation)
  + [End-To-End Quoting](#end-to-end-quoting)
  + [Chunked Payments](#chunked-payments)
* [Model of Operation](#model-of-operation)
  + [Informational Quote](#informational-quote)
  + [Single Payment](#single-payment)
  + [Chunked Payment](#chunked-payment)
* [Specification](#specification)
  + [Encryption](#encryption-1)
  + [Data Packet](#data-packet)
* [Appendix A: Advanced Sender Features](#appendix-a-advanced-sender-features)

## Overview

Like [PSKv1](./0016-pre-shared-key/0016-pre-shared-key.md), PSKv2 uses a secret shared between the sender and receiver to generate the conditions and fulfillments for payments without repeated end-to-end communication. PSKv2 can be used for individual or streaming micropayments and also includes support Chunked Payments.

This specificiation aims to standardize the behavior of receivers while allowing for sophisticated sender behavior to be developed in the future. [Appendix A: Advanced Sender Features](#appendix-a-advanced-sender-features) outlines areas for potential sender features to be implemented in the future.

### Setup

Before using PSKv2, the sender and receiver use an authenticated, encrypted communication channel (generally provided as part of an [Application Layer Protocol](./0001-interledger-architecture/0001-interledger-architecture.md#application-layer)) to exchange:

- PSK version (such as `2.0` for this version)
- A 32-byte random or pseudorandom shared secret
- The receiver's ILP address

The receiver MAY generate the shared secret from a longer-term secret and a nonce, as described in [PSKv1's Appendix A: Recommended Algorithm for Generating Shared Secrets](./0016-pre-shared-key/0016-pre-shared-key.md#appendix-a-recommended-algorithm-for-generating-shared-secrets). In this case, the receiver would append the nonce (**not** the secret) to their ILP address to create the destination address they communicate to the sender.

### Encryption

In PSKv2.0, request and response data is encrypted using [AES-256-GCM](https://en.wikipedia.org/wiki/Galois/Counter_Mode) with a 12-byte Initialization Vector (IV) and a 16-Byte Authentication Tag.

If subsequent versions support additional encryption algorithms, those details should be exchanged between the sender and receiver when they establish the pre-shared key. If a receiver attempts to decrypt an incoming packet but is unable to (perhaps because the sender is using an unsupported cipher), they SHOULD reject the incoming transfer with an `F06: Unexpected Payment` error.

### Condition and Fulfillment Generation

The sender and receiver generate the condition and fulfillment using the pre-shared key that gives this protocol its name. The fulfillment is computed from the pre-shared key and the encrypted PSK data. The condition is the hash of the fulfillment.

As in PSKv1, this method for generating the condition and fulfillment enables many payments to be sent without end-to-end communication for each one. However, because the sender also knows the fulfillment up-front, neither version of PSK allows the sender to use the fulfillment as a non-repudiable proof of payment. For use cases where this is desired, a Transport Protocol like the [Interledger Payment Request (IPR)](./0011-interledger-payment-request/0011-interledger-payment-request.md) should be used instead.

### End-To-End Quoting

In contrast to PSKv1, which depends on the [Interledger Quoting Protocol (ILQP)](./0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md), PSKv2 has two built-in mechanisms for discovering the exchange rate of a given path: informational quotes and dynamic price discovery.

For purely informational quotes, PSKv2 uses unfulfillable test payments to the receiver to determine the exchange rate for a given path. The condition is set to a random 32-byte condition (with no known fulfillment). When the receiver gets the incoming payment, they reject the incoming transfer and include in their response how much arrived in that transfer. The sender can use the source amount they set and the receiver's response to determine the rate.

When a sender is sending many payments to the receiver, they need a dynamic view of the exchange rate because the rate may change during the course of the interaction. To handle these cases, every PSKv2 payment response includes the amount that arrived in the final transfer to the receiver. Similar to the informational quotes, the sender can use the chunk source amount and the receiver's response to determine and monitor the exchange rate.

**Judging Prices by Source Units:** With any type of Interledger quoting, whether end-to-end or using ILQP, senders SHOULD judge prices in their source units. Receivers can lie about how much arrives in a test payment for a quote or they could run their own ledger and connector that happen to have a bad exchange rate. Therefore, senders must assume that whatever amount the receiver says has arrived represents the "real" rate of the path.

**Linear Exchange Rates and Fixed Destination Amount Quotes:** End-to-End Quoting works best with linear exchange rates. If the rate for a path is linear, it can be determined by sending a single test payment for an arbitrary amount. The source amount required to deliver a fixed destination amount can be easily determined by dividing the source amount by the rate. If exchange rates are non-linear, getting an informational quote for a fixed destination amount would require a binary search, which is not ideal. However, in an Interledger network primarily or exclusively suited to small payments, there should be little reason for rates to vary by payment size.

### Chunked Payments

PSKv2 is designed to support both "chunked" and "streaming" payments. Both involve sending many small payment chunks to pay for some interaction. "Chunked Payments" refers to splitting one larger transaction into smaller chunks, for example sending $1000 as one thousand $1 payments. Chunked payments are useful for dealing with paths that have low Maximum Payment Sizes (MPS). "Streaming Payments" refers to sending payment chunks in exchange for an ongoing service, for example paying for a movie stream 1 Mb at a time.

Interledger connectors set their Maximum Payment Size (MPS) based on their available liquidity, the "bandwidth" they allocate to each of their peers, and the risk they are willing to take on each payment. Analogous to the Internet's Path Maximum Transmission Unit (MTU), an Interledger path MPS is the minimum MPS of the connectors involved.

If senders want to use a path with an MPS lower than their payment amount, they need to split their payment into chunks. PSKv2 includes a Payment ID and Sequence number to enable receivers to associate incoming payment chunks properly.

**Possibility for Incomplete Payments:** If the path between the sender and receiver runs out of liquidity while a chunked payment is in progress, it could be impossible for the payment to complete fully. This should be a rare case, analogous to Internet Service Providers getting cut off because they fail to pay their electricity bills. However, in such cases, the receiver may need to refund the partial payment by sending another chunked payment back and either the sender or receiver would incur the transaction costs.

**Fluctuating Exchange Rates:** The rate from the sender to the receiver may change due to legitimate market movements during the course of a payment. Senders SHOULD monitor the rate changes and they may not want to send payments that are significantly larger than their bandwidth (this could be compared to how downloading an ultra high-definition movie over a dial-up connection is possible but would not make for a good experience).

**Malicious Connectors:** Exchange rates can also change for illegitimate reasons, such as connectors driving up the price mid-payment. Ultimately, the main force keeping connectors' rates low is competition. If there is only one path, the connectors can raise the rate without resorting to any sneaky tactics and the sender would need to decide if they are willing to pay that rate. If a sender has multiple options for the connector they send through, they may want to use [Multi-Path Chunked Payments](#multi-path-chunked-payments) to automatically switch paths if one becomes more expensive.

**Trusting the Receiver:** The sender of a payment must always trust the receiver, except in the rare case that they are doing an atomic exchange of money for goods or services. Whether or not the sender is sending a single- or multiple-chunk payment, a malicious receiver could simply refuse to deliver the goods or services once the payment arrives. If senders must trust the receivers anyway, it is no worse to trust receivers to accurately report how much money arrived and not collude with connectors to raise the rates mid-payment. Since senders will judge merchants' prices by the total source amount they pay, receivers that pull such tricks should develop negative reputations and be avoided.

## Model of Operation

### Informational Quote

1. Sender creates a packet with a type of 1, a random Payment ID, a Sequence number of 0 (or the next Sequence if the quote is part of a multi-chunk payment), and both the Payment Amount and Chunk Amount set to 2^64 - 1 (the maximum unsigned 64-bit integer, or 18446744073709551615). Sender [encrypts](#encryption-envelope) the packet.
2. Sender generates a random 32-byte condition.
3. Sender sends a test payment with the condition, encrypted data and either the chosen source amount (in the case of a fixed source amount payment) or an arbitrary amount (in the case of a fixed destination amount).
4. Receiver is notified of the incoming transfer and decrypts the data.
5. Receiver compares the Chunk Amount from the packet with the incoming transfer amount and notes that the incoming transfer amount is too low.
6. Receiver creates a response packet, including the Payment ID and Sequence from the request, a Payment Amount of 0 (or the total they have fulfilled with this Payment ID), and the Chunk Amount set to the amount that arrived on the incoming transfer. Receiver [encrypts](#encryption-envelope) the packet.
7. Receiver rejects incoming transfer, setting the rejection message's data to the encrypted quote response.
8. Sender decrypts the quote response and divides the receiver's Chunk Amount by the source amount to determine the path exchange rate.

### Single Payment

1. In the case of a fixed source amount payment, sender multiplies the source amount by the rate to determine the Payment Amount. In the case of a fixed destination amount payment, sender divides the destination amount by the rate to determine the amount for their outgoing transfer.
2. Sender creates a packet with a Type of 1, a random Payment ID, a Sequence number of 0, and the Payment Amount and Chunk Amount set to the destination amount determined in step 2. Sender [encrypts](#encryption-envelope) the request.
3. Sender generates the payment condition as described [below](#fulfillable-condition).
4. Sender sends a payment using the source amount determined in step 2, the condition from step 3, and the encrypted request as the data.
5. Receiver is notified of the incoming transfer and decrypts the data.
6. Receiver checks to ensure that the incoming transfer amount is greater than or equal to the Chunk Amount specified in the request. If the Payment Amount is not equal to 0, the receiver checks that the transfer amount is less than or equal to the Payment Amount specified in the request.
7. Receiver creates a [Payment Chunk Response](#payment-chunk-response) with the same Payment ID and Sequence number. The Payment Amount and Chunk Amount are set to the amount that arrived on the incoming transfer. The receiver then [encrypts](#encryption-envelope) the data.
8. Receiver generates fulfillment as described [below](#fulfillment-generation) and fulfills the incoming transfer with the fulfillment and the encrypted response data.
9. Sender is notified of the outgoing transfer being fulfilled and can use the decrypted response to determine the amount that arrived at the destination.

### Chunked Payment

1. Sender creates a packet with Type 0, a random Payment ID, a Sequence number of 0 and a Chunk Amount of 0. In the case of a fixed destination amount, sender sets the Payment Amount to the destination amount. In the case of a fixed source amount, sender sets the Payment Amount to 2^64 - 1 (the maximum unsigned 64-bit integer, or 18446744073709551615). Sender [encrypts the request](#encryption-envelope).
2. Sender generates the payment condition as described [below](#fulfillable-condition).
3. Sender sends a payment with the condition from step 2., the encrypted request from step 1. as the data, and an arbitrary source amount.
4. Receiver is notified of the incoming transfer and decrypts the data.
5. Receiver checks that the incoming transfer amount is greater than or equal to the Chunk Amount and that the total that has arrived thus far does not exceed the Payment Amount.
6. Receiver creates a response packet with the Type 2, the same Payment ID, Sequence. The Payment Amount is set to the total the receiver has received and fulfilled thus far (including the current chunk). Receiver sets the Chunk Amount to the amount that arrived on the incoming transfer. Receiver [encrypts the response](#encryption-envelope).
7. Receiver generates fulfillment as described [below](#fulfillment-generation) and fulfills the incoming transfer.
8. Sender is notified of the outgoing transfer being fulfilled and decrypts the attached data.
9. Sender determines the exchange rate by dividing the Chunk Amount from the receiver by the chunk's source amount.
10. Sender repeats step 1-8 with the following modifications, until the fixed source or destination amount has been sent or delivered, respectively:
  - Sender MUST create a new PSK data packet for each chunk with the same Payment ID and an incremented Sequence number (the Sequence enables the sender to reliably correlate outgoing requests with their responses)
  - Sender MAY specify the minimum Chunk Amount the receiver should accept for each transfer based on the calculated path exchange rate
  - Sender MAY adjust the transfer amount upwards or downwards in response to successful and unsuccessful payments, or to deliver a fixed destination amount exactly
  - Sender SHOULD set the Type to 1 on the last chunk. Receivers SHOULD NOT fulfill additional chunks after a Type 1 chunk has been received. Note that receivers SHOULD stop fulfilling chunks after the specified Payment Amount has been reached, even if the sender did not send a Type 1 packet.

## Specification

### Encryption

Request and response data are encrypted using [AES-256-GCM](https://en.wikipedia.org/wiki/Galois/Counter_Mode) with a random 12-byte Initialization Vector (IV) and a 16-byte Authentication Tag.

#### Encryption Envelope

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
iv = random_bytes(16)
encryption_key = hmac_sha256(shared_secret, "ilp_psk_encryption")
{ ciphertext, auth_tag } = aes_256_gcm(encryption_key, iv, data)
```

### Data Packet

All PSKv2.0 requests and responses encode their data in the same byte format, though the meanings of the fields differ depending on whether it is a request or a response.

The following is encrypted, as defined [above](#encryption), and set as the ILP payment data on a payment from the sender to the receiver.

```
(Numbers represent bytes)

       4       8       12      16      20      24      28      32
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|T|           Payment ID          |  Seq  | Payment Amount| Chu-|
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|nk Amount|             Application Data                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Application Data                        |
\                                                               \
\                                                               \
|                       Application Data                      |E|
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          Junk Data                            |
\                                                               \
\                                                               \
|                          Junk Data                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

#### Packet Types

| Type ID | Description |
|---|---|
| `0` | Payment chunk. May be carried on a fulfillable transfer (in the case of a payment) or an unfulfillable transfer (in the case of a quote). |
| `1` | Last payment chunk. Same as `0` but indicates that there will be no more chunks after this one is fulfilled. |
| `2` | Success response. Must be carried on the data accompanying the fulfillment. |
| `3` | Error response. Must be carried in the error with which the receiver rejects the incoming transfer. |

#### Request Fields

| Field | Type | Description |
|---|---|---|
| Type (T) | 1-Byte UInt (UInt8) | `0` to indicate a payment chunk, `1` to indicate it is the last chunk for the payment. Receivers SHOULD NOT fulfill additional chunks for the given payment after the last chunk has been received |
| Payment ID | 16-Byte UInt | Unique ID of this payment |
| Sequence | 4-Byte UInt (UInt32) | Zero-indexed chunk sequence number. Receivers SHOULD NOT fulfill two chunks with the same sequence for a single payment. Receivers SHOULD use the sequence to order chunks in case application data is split across multiple chunks, but chunks do not necessarily need to be delivered in order |
| Payment Amount (Total)* | 8-Byte UInt (UInt64) | The total amount the payment is intended to deliver. A value of `0` in a request indicates that the sender will determine when to stop sending chunks |
| Chunk Amount (Minimum) | 8-Byte UInt (UInt64) | Minimum amount the receiver should receive for this chunk in order to fulfill it. A value of `0` in a request indicates that any amount should be accepted |
| Application Data | [OER Variable-Length Octet String](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) | User data carried along with the payment |
| Extensions (E) | 1-Byte UInt (UInt8) | Currently set to `0`. Reserved for future use to indicate the presence of extension fields. Parsers that do not understand the extensions MUST ignore them |
| Junk Data | 0-? Bytes | _(Optional)_ Extra data included to obscure what the ILP payment is for. Receivers MUST ignore this data. Senders SHOULD include either the maximum or a random number of empty (0) bytes |

\* **Note:** The largest Payment Amount (the sum of all of the chunks) supported by PSKv2.0 is the maximum value for a UInt64 or 18446744073709551615.

#### Response Fields

The following apply to both fulfillment and error responses:

| Field | Type | Description |
|---|---|---|
| Type (T) | 1-Byte UInt (UInt8) | `3` to indicate it is a fulfillment response, `4` to indicate it is an error |
| Payment ID | 16-Byte UInt | Unique ID from the request. Senders SHOULD ensure that the response ID matches the request |
| Sequence | 4-Byte UInt (UInt32) | Chunk sequence number from the request. Senders SHOULD ensure that the sequence matches the request |
| Payment Amount (Total Received) | 8-Byte UInt (UInt64) | The amount the receiver has received thus far for the payment (the sum of fulfilled chunks). If a chunk exceeds the Payment Amount specified in the request, this value in the response MUST NOT include the chunk being rejected |
| Chunk Amount (Received) | 8-Byte UInt (UInt64) | The amount the receiver received for the given chunk |
| Application Data | [OER Variable-Length Octet String](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) | User data carried along with the payment |
| Extensions (E) | 1-Byte UInt (UInt8) | Currently set to `0`. Reserved for future use to indicate the presence of extension fields. Parsers that do not understand the extensions MUST ignore them |
| Junk Data | 0-? Bytes | _(Optional)_ Extra data included to obscure what the ILP payment is for. Receivers MUST ignore this data. Senders SHOULD include either the maximum or a random number of empty (0) bytes |

#### Condition Generation

There are two methods the sender can use to generate the condition, depending on whether they want the payment to be fulfillable or not.

##### Unfulfillable Condition

If the sender does not want the receiver to be able to fulfill the payment (as for an informational quote), they can generate an unfulfillable random condition.

```
condition = random_bytes(32)
```

##### Fulfillable Condition

If the sender does want the receiver to be able to fulfill the condition, the condition MUST be generated in the following manner.

The `shared_secret` is the pre-shared key that gives this protocol its name. The `data` is the **encrypted** payment chunk request.

```
hmac_key = hmac_sha256(shared_secret, "ilp_psk2_fulfillment")
fulfillment = hmac_sha256(hmac_key, data)
condition = sha256(fulfillment)
```

#### Fulfillment Generation

The following pseudocode details how the receiver regenerates the fulfillment from the data.

**Note:** Senders MAY use unfulfillable conditions to get an informational quote. Receivers MUST return an [Error Response](#response-fields) packet that includes the amount that arrived on the incoming transfer, even if they are unable to regenerate the fulfillment from the request.

The `shared_secret` is the pre-shared key that gives this protocol its name. The `data` is the **encrypted** payment chunk request.

```
hmac_key = hmac_sha256(shared_secret, "ilp_psk2_fulfillment")
fulfillment = hmac_sha256(hmac_key, data)
```

## Appendix A: Advanced Sender Features

Inspired by TCP, PSKv2 aims to standardize how receivers should react to incoming packets while leaving room for senders to utilize more sophisticated behavior. The following are areas for further development:

#### Path Maximum Payment Size (MPS) Discovery

Senders may want to discover the Maximum Payment Size (MPS) a given Interldger payment path supports to send a chunked payment as quickly as possible (this is analogous to the Internet's [Path Maximum Transmission Unit (MTU)](https://en.wikipedia.org/wiki/Path_MTU_Discovery)). The path MPS limit may be static, such as if connectors limit the size of payments to manage the risk posed by [fulfillment failure](./0018-connector-risk-mitigations/0018-connector-risk-mitigations.md#fulfillment-failure), or it may be dynamic if connectors regularly settle their bilateral relationships and set their MPS based on available liquidity. In either case, senders may vary their payment sizes to determine the maximum supported by the path (at a particular moment) and they may cache the result to use as a starting point for the next payment.

#### Congestion Control

If connectors dynamically adjust the payment bandwidth they allocate to their peers, senders may need to use congestion avoidance strategies like those in TCP to avoid sending more payment volume than the path can handle. It is even possible that there are sufficient parallels between Interledger liquidity and Internet bandwidth to apply specific algorithms such as [TCP CUBIC](http://www4.ncsu.edu/~rhee/export/bitcp/cubic-paper.pdf) for determining how fast to increase or decrease the payment chunk size.

#### Multi-Path Chunked Payments

If senders have connections to multiple connectors, they can send chunks of a single payment through multiple paths. The can monitor the exchange rate, latency, and reliability of each of the paths and adjust the amount of traffic they are sending through each path according to the priority they place on speed versus cost.

#### Exchange Rate Optimization

As it is possible for the exchange rate to fluctuate while a chunked payment is being sent, senders may change their behavior to improve the exchange rate they get for their payment. Senders could attempt to predict market conditions and delay individual chunks until the rate improves. Senders could also specify a relatively high minimum amount the receiver should accept to execute the payments only when the exchange rate is the best.

#### Data Transmission Over ILP

If Interledger payments are fast enough, applications could choose to send both value and data over ILP. Receivers can use the Payment ID and Sequence to order the data received on each payment chunk. Senders could split their payment up based on value as well as the maximum amount of data each chunk can carry.
