# Interledger Payment Request (IPR)

## Preface

This document specifies the Interledger Payment Request (IPR) transport protocol. It is an end-to-end protocol in which the receiver of an Interledger payment first communicates a request for payment to the sender. This document also details how the receiver can verify that incoming payments match previously created requests without storing a history of all outstanding requests.

## Introduction

### Motivation

The Interledger Protocol uses holds based on cryptographic conditions and expiries to ensure a sender's funds are delivered to the destination or returned to the sender's account.

One approach is for conditions to be generated and fulfilled by the receivers of Interledger payments. When the sender of the payment receives the fulfillment, they can be certain that the receiver received the payment.

Receiver-generated conditions are also useful in building non-repudiable application layer protocols. The receiver would generate the condition and cryptographically sign a statement that the preimage of the specified hash indicates the sender has settled a particular debt. The receiver would only disclose the hash preimage upon receipt of payment. Once the sender gets the preimage, they would be able to demonstrate to 3rd parties that they paid the receiver using the preimage and the original signed statement.

In most cases, non-repudiability is unnecessary, as it is sufficient for the sender to get proof that the receiver received the payment even if that proof cannot be used to convince 3rd parties. In such cases, the [Pre-Shared Key](../0016-pre-shared-key/0016-pre-shared-key.md) transport protocol is recommended because it does not require end-to-end communication for each payment.

### Scope

This document defines a suggested format for representing payment requests and an approach for receiver-generated conditions. Protocols built on top of IPR MAY use the format provided here, though they can use any format they choose instead.

While this document also provides a recommendation for generating transfer conditions, conditions are often opaque to all parties aside from the receiver. Receivers MAY use any condition they choose, however this specification includes best practices that receivers SHOULD take into consideration.

This document does **not** specify how payment requests are communicated from a receiver to a sender.

### Model of Operation

Interledger Payment Requests are intended to be used in higher-level protocols as follows:

1. Receiver creates the ILP Packet and generates the condition using one of algorithms outlined in [Condition Generation](#condition-generation).
2. Receiver communicates the ILP Packet and condition to the sender.
3. Sender prepares a local ledger transfer to a connector, held pending the execution condition provided by the receiver and with the ILP Packet provided by the receiver attached.
4. Connectors forward the payment until it reaches the receiver.
5. Receiver receives a notification of a held transfer with an ILP Packet attached.
6. Receiver checks the transfer amount against the ILP Packet and checks the payment request has not expired.
7. Receiver regenerates the condition and fulfillment from the ILP Packet attached to the incoming transfer, using the same algorithm as before, and fulfills the transfer's condition. If the condition generated does not match the one in the transfer it means that the ILP Packet has been tampered with and the transfer goes unfulfilled.

## Payment Request Specification

### JSON

```json
{
  "packet": "AYGyAAAAAAAAAAo6ZXhhbXBsZS5pbHBkZW1vLmJsdWUuYm9iLkR0azB1Y3U4OHFJQm1iRFEwelhxa2lkTWZhOHRQakJZUW1QU0svMS4wCk5vbmNlOiBvdHotT25NbThURHo3NThGYWY4cXRRCkVuY3J5cHRpb246IGFlcy0yNTYtZ2NtIEdFRUR0MXk4NmlkSVFMa2xWbnpiRWcKCuXPle38YB02KVAHPtVNqRgP7Ok6D-QRAA",
  "condition": "oHeVy7WAEhrJF3U4NeLt5QT6Fr3L2YeBCmB88Xu9sEY"
}
```

| Field | Type | Short Description |
|:--|:--|:--|
| `packet` | [Base64-Url](https://en.wikipedia.org/wiki/Base64#URL_applications) Encoded ILP Packet | ILP Payment packet including the destination address and amount |
| `condition` | 32 Bytes, Base64-Url Encoded | Execution condition for the payment |

In IPR the sender only uses the `account` and `amount` from the ILP packet and MUST treat the `data` as opaque. The sender MUST NOT modify the ILP packet at all, or the receiver will reject the payment.

### Binary

**TODO**

## Condition Generation

It is RECOMMENDED that receivers use a Message Authentication Code (MAC) of the details of their payment request in the condition so that the condition can be used as an integrity check on incoming transfers. This allows a receiver to ensure that a transfer matches a request they previously generated, without the receiver needing to maintain a log of all outstanding payment requests.

Receivers MUST include a payment request-specific nonce in the ILP packet to ensure that conditions are unique per-request.

Receivers SHOULD include an expiry date so that they do not accept incoming payments that are paid too long after their creation.

### Using a PSK Implementation

It is RECOMMENDED that receivers use an implementation of the [Pre-Shared Key](../0016-pre-shared-key/0016-pre-shared-key.md) protocol to generate the packet and condition for IPR.

The receiver should follow BOTH the steps normally followed by the receiver AND sender. The receiver should generate the secret in the normal fashion but MUST NOT share it. The receiver then follows the steps the sender would do in a PSK payment to create the packet and condition from the secret and the payment parameters.

For details, see the [Pre-Shared Key Pseudocode](../0016-pre-shared-key/0016-pre-shared-key.md#pseudocode).

Note the receiver's use of a PSK implementation does not matter to the sender, because the sender treats the `data` in the ILP packet as opaque and uses the condition from the receiver without needing to know how the fulfillment is generated.

