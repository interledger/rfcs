---
title: Interledger Payment Requests (IPR) v3
draft: 1
---
# Interledger Payment Request (IPR) v3

The Interledger Payment Request (IPR) transport protocol version 3 is based on the idea of loop-back ILP payments as described in [Loopback Transport Protocol - IL RFC 29](). In IPRv3 the receiver of an Interledger payment communicates an `InterledgerPrepare` packet, addressed to themselves, to the sender. The sender then routes this packet over the Interledger to complete a payment to the receiver. This document also recommends a method for receivers to generate the initial `InterledgerPrepare` packet (the payment request) such that they can verify incoming payments without storing all outstanding requests.

## Introduction

### Motivation

The Interledger Protocol uses cryptographic conditions and expiries to ensure a sender's funds are delivered to the correct destination or returned to the sender's account.

One way to set this up is for conditions to be generated and fulfilled by the receiver of the Interledger packets. When the sender of the payment receives the fulfillment, they can be certain that the receiver received the payment.

Receiver-generated conditions are also useful in building non-repudiable application layer protocols. The receiver generates the condition and cryptographically signs a statement that the preimage of the specified hash indicates the sender has settled a particular debt. The receiver would only disclose the hash preimage upon receipt of payment. Once the sender gets the preimage, they would be able to demonstrate to third parties that they paid the receiver using the preimage and the original signed statement.

In many cases, non-repudiability is unnecessary, as it is sufficient for the sender to get proof that the receiver received the payment even if that proof cannot be used to convince third parties. In such cases, the [Pre-Shared Key](../0025-pre-shared-key-2/0025-pre-shared-key-2.md) transport protocol may be preferred.

### Scope

This document defines a suggested format for representing payment requests (as ILP packets) and an approach for receiver-generated conditions. Protocols built on top of IPR MAY use the format provided here, though they can use any format they choose instead.

While this document also provides a recommendation for generating conditions, conditions are often opaque to all parties aside from the receiver. Receivers MAY use any condition they choose, however this specification includes best practices that receivers SHOULD take into consideration.

This document does **not** specify how payment requests are communicated from a receiver to a sender. A number of use case options exist, some of which are described in the [Loopback Transport Protocol - IL RFC 29]().

### Model of Operation

The assumption, when creating an IPR, is that the receiver is requesting a payment from the sender. This can be modelled as an account between the sender and receiver where the balance is currently in favour of the receiver by at least the amount they wish to receive.

Therefor, just like the accounts between any two ILP peers, this balance can be adjusted by the successful exchange of an ILP packet between the peers. To that end, the payment request from the receiver takes the form of an `InterledgerPrepare` packet for a payment from the receiver to the sender which will settle the account between them if it is fulfilled.

The sender can then forward this packet back to the receiver via the Interledger network and, in so doing, get back the fulfillment of the packet. That fulfillment validates the ILP packet sent from the receiver, effectively reducing the balance owed from the sender to the receiver by the amount in the original ILP packet (the payment request).

The flow goes as follows:

1. The receiver creates the payment request, an `InterledgerPrepare` packet, with:
    1.  the `amount` that is being paid from the sender to the receiver (in the receiver's currency and scale),
    2.  a `destination` ILP Address that routes to the receiver (and may contain a payment specific suffix to help the receiver identify it when it arrives),
    3.  an `executionCondition` generated using one of algorithms outlined in [Condition Generation Recommendations](#condition-generation-recommendations),
    4.  an appropriate `expiresAt` that will allow the sender to both, determine the appropriate amount to send (a process that could potentially take some time), and complete the payment, and
    5.  optional application `data` that is opaque to the sender.
2. The receiver sends the payment request (the `InterledgerPrepare` packet) to the sender.
3. The sender routes this packet out via one of its ILP peers, behaving like a typical ILP connector, and MUST therefor:
    1.  determine the appropriate `amount` to send on the next hop,
    2.  determine an appropriate `expiresAt` to use on the next hop, and 
    3.  copy the `destination`, `executionCondition` and `data`as is.
4. Assuming the packet is successfully routed to the receiver, they compare the amount received to the amount they expect and then either fulfill or reject the payment.
5. When the sender receives the fulfillment they MAY pass this on the receiver, although this is not structly necessary as the receiver generated the fulfillment.

## Condition Generation Recommendations

It is RECOMMENDED that receivers follow a similar algorithm to the one described below to generate the packet and condition, because it will already include the best practices for generating conditions and enable the receiver to avoid keeping state of all outstanding payment requests.

Note, the receiver's method for generating the condition or encoding data in the ILP packet does not matter to the sender. The sender treats the `data` in the ILP packet as opaque and uses the condition without needing to know how the fulfillment is generated.

### Recommended Implementation

To avoid keeping state the algorithm uses a signature over the payment details (or part thereof) as the fulfillment. This allows the receiver to regenerate the fulfillment from the payment details when the `InterledgerPrepare` packet arrives.

Depending on the requirements the signature could be be:
1. generated using a private key that is part of a key pair for which the public key is known to the sender, and the private key is known to be controlled by the receiver.
2. a simple HMAC over the payment details where the key is known only to the receiver (and likely unique per sender).

To generate the fulfillment and condition, the receiver follows these steps:

1. Let `base-address` be the ILP address of the receiver's account that this payment will be routed to. The same address MAY be used for multiple payments and multiple senders.
2. Let `nonce` be a randomly generated 12-byte value
3. Let `destination-address` be `base-address` concatenated with a tilde `~` and the 16 ASCII characters that represent the base64-encoded `nonce`
3. Let `minimum-receive-amount` be the minimum amount that the receiver will accept for this payment, expressed as a UInt64 in the scale and currency of the account represented by `base-address`.
4. Let `payment-expiry` be a date and time, after which, the receiver will reject this payment.
5. Let `signature-packet` be an OER encoded `InterledgerPrepare` packet where:
    1. `amount` is `minimum-receive-amount`,
    2. `expiresAt` is `payment-expiry`,
    3. `executionCondition` is 32 bytes, all with a value of zero (0x00),
    3. `destination` is `destination-address`, and
    4. `data` is empty.
5. Let `signature` be a signature over `signature-packet` generated using one of the methods described in [Signature Generation Recommendations](#signature-generation-recommendations).
6. Let `fulfillment` be a 32-byte buffer containing `signature` (or the first 32 bytes of `signature` if it is larger than 32-bytes). If signature is smaller than 32 bytes, pad the remaining buffer with zeros (0x00).
7. Let `condition` be the SHA-256 hash of `fulfillment`.

To remain stateless the receiver must send the `minimum-receive-amount` and `payment-expiry` in the `data` of the payment request so that it can extract them from the incoming `InterledgerPrepare` which will have an `amount` and `expiresAt` set by the preceding connector. These values are required, to re-create the fulfillment, but also to ensure the incoming payment `amount` and `expiresAt` are acceptable. These values can simply be concatenated and sent as the `data` of the payment request however it is RECOMMENDED that they are first encrypted to enhance the security of the payment.

The receiver may also wish to attach additional application layer data to each ILP packet, for example if multiple packets are sent to complete a single large payment (chunked payments) an identifer of the larger payment or invoice might be included.

As the data will be encrypted and decrypted by the same system (the receiver) any safe encryption function may be used and selection of an appropriate algorithm is outside the scope of this specification. It is RECOMMENDED that the `nonce` value is included in the data that is encrypted to ensure variability.

A RECOMMENDED format for the input data into the encryption function is the OER encoded data given by the following ASN.1 definition:

```asn
PlainTextData ::= SEQUENCE {
    minimumAmount UInt64,
    expiresAt Timestamp,
    nonce UInt96,
    applicationData OCTET STRING (SIZE (0..32728))
}
```

### Alternative Methods and General Best Practices

Receivers MAY use any method they choose for generating the condition, such as using a random fulfillment for each payment request. The receiver MUST be able to identify and verify the incoming `InterledgerPrepare` packet for every outstanding, requested payment and produce the corresponding fulfillment. The recommended implementation handles these requirements, without storing every fulfillment and packet in a database, by using the condition as a Message Authentication Code (MAC) of the payment request and encoding the random `nonce` as part of the address.

Receivers SHOULD follow these guidelines if implementing a custom system:
* Receivers SHOULD include a payment request-specific nonce in the ILP packet to ensure that conditions are unique even when multiple payments would otherwise have identical packets.
* Receivers SHOULD include an expiry date so that they do not accept incoming payments that are paid too long after their creation.

# Signature Generation Recommendations

Part of the recommended algorithm for generating the condition includes generating a signature over the payment data which takes the form of an `InterledgerPrepare` packet with a blank condition and application data called the `signature-packet`.

The `signature` over the `signature-packet` can be derived in various ways depending on the context of the payment. In systems where it is important to tie the identity of the receiver to the fulfillment for the purpose of irrepudiability the signature may be generated using a private key and asymmetric cryptographic signing algorithm whereas if the requirements are simply that the fulfillment can only be produced by the receiver, a simple HMAC using a key known only to the receiver may suffice.