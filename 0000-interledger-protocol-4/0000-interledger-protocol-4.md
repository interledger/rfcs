---
title: Interledger Protocol V4 (ILPv4)
draft: 1
---

# Interledger Protocol V4

Interledger is a protocol for sending packets of money across different payment networks or ledgers. ILPv4 is a simplification of previous versions of the protocol designed primarily for "penny switching", or routing large volumes of smaller-value packets. ILPv4 can be integrated with any type of ledger, including those not built for interoperability, and it can be used with a variety of higher-level protocols that implement features ranging from quoting to sending larger amounts of value with chunked payments. 

## Overview

### Design Goals

- **Neutrality** - Interledger is not tied to any company, currency, or network.
- **Interoperability** - ILP should be usable across any type of ledger, even those that were not built for interoperability.
- **Security** - Senders, connectors, and receivers should be protected from one another and especially isolated from risks posed by parties that they are indirectly connected to.
- **Simplicity** - The core ILP should be as simple as possible. There is room for significant variability at lower and higher layers of the [Interledger stack](../0001-interledger-architecture/0001-interledger-architecture.md#interledger-protocol-suite), but the Interledger layer is the one part where widespread agreement is needed for interoperability.
- **End-to-End Principle** - Inspired by the Internet, any features that do not need to be implemented by the core protocol and network should be built into the edges of the network (the sender and receiver).

### Relation to Other Protocols

ILPv4 packets may be sent over any communication channel between peers. Payment obligations created by ILP packets may be settled using any available means, ranging from ledger transfers triggered by an API, to signed updates to payment channels, or the physical delivery of cash or other goods.

ILPv4 will probably be used with a Transport Layer protocol such as the Pre-Shared Key V2 (PSKv2) protocol, which handles the generation of ILP conditions and fulfillments.

### Differences from Previous Versions of ILP

- **Designed for Smaller, More Homogenous Packet Amounts** - ILPv4 applies a number of simplifications based on the change from supporting all packet amounts to focusing the Interledger layer on lower-value packets. Larger amounts can be sent using chunked payments, but the core network is optimized for sending large volumes of small packets. This renders unnecessary some of the more complex features of previous versions like Liquidity Curves for expressing how exchange rates may vary depending on the packet amount. Lower-value packets also help to minimize [connector risks](../0018-connector-risk-mitigations/0018-connector-risk-mitigations.md).
- **Payment Channels, Not On-Ledger Escrow** - Since ILPv4 is optimized for smaller packets, speed and cost are of greater importantance than in previous versions. ILPv4 uses ledgers or payment channels for settling bilateral payment obligations but ILPv4 packets are sent just between connectors, rather than through the underlying ledgers themselves. This enables packet timeouts to be short, because they do not need to include the processing time of slower ledgers, which further reduces [connector risks](../0018-connector-risk-mitigations/0018-connector-risk-mitigations.md).
- **Forwarding, Not Delivery** - In contrast to the first version of ILP, ILPv4 does not have the destination amount in the packet and connectors must only apply their local rate to forward packets. Senders may use higher-level protocols to indicate to the receiver the minimum amount they should accept for each packet, but this is no longer built into the core protocol. Connectors have only one simple behavior and do not need to maintain up-to-date price information on all possible destintations.
- **Quoting is an Application Concern** - Connectors are only responsible for forwarding ILP packets and do not need to implement a [separate protocol for quoting](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md). Applications can use test packets to determine the exchange rate of a particular path.

## Flow

Before the protocol starts, the sender and receiver use a higher-level protocol to agree on the destination account and packet condition.

1. Sender constructs an ILP Prepare packet with the receiver's destination account, the agreed-upon condition, and an amount and expiry of their choice. The sender may include additional data, the formatting of which is determined by the higher-level protocol.
2. Sender sends the ILP Prepare packet to a connector over some communication channel, such as a Websocket. 
3. Connector checks whether the sender has sufficient bandwidth (balance or credit) to send the amount specified in the packet. If so, the connector reduces the sender's bandwidth by the value of the packet. If not, the connector returns an ILP Reject packet.
4. Connector uses the destination ILP address from the packet and its local routing tables to determine which next hop to forward the packet to.
5. Connector modifies the packet amount and expiry to apply their exchange rate and shorten the expiry time.
6. Connector forwards the packet to the next hop, which may be another connector. All subsequent connectors go through steps 3-6 until the packet reaches the receiver.
7. Receiver checks the ILP Prepare packet, according to whatever is stipulated by the higher-level protocol (such as checking whether the amount received is above some minimum specified by the sender). 
8. Receiver returns an ILP Fulfill packet, containing the preimage of the condition in the ILP Prepare packet. The receiver may include additional data, the formatting of which is determined by the higher-level protocol.
9. Connector checks that the receiver has returned the fulfillment before the expiry in the ILP Prepare packet. If so, the connector returns the same ILP Fulfill packet to the previous connector and credits the receiver's account with the amount in the ILP Prepare packet. If the Prepare has expired, the connector returns an ILP Reject packet to the previous connector. Each connector repeats this step until the Fulfill (or Reject) packet reaches the sender.
10. Sender checks that the preimage in the ILP Fulfill packet matches the condition in their Prepare packet and may read any data returned by the receiver.
11. Sender signs an update to their payment channel with the first connector to cover the value of the ILP Prepare (or they may settle less frequently using slower on-ledger transfers or physical deliveries of cash or other goods) and communicates it to the connector.
12. Connector validates the sender's signed payment channel update (or other proof of settlement) and increases the sender's bandwidth by the amount they paid. If the sender does not pay for the ILP Prepare, the connector may refuse to process further ILP packets until they do or the connector may block that user entirely.

## Specification

### Packet Format

ILPv4 packets SHOULD be encoded using the ASN.1 Octet Encoding Rules.

#### Type-Length Wrapper

All ILP packets are wrapped in the following envelope:

| Field | Type | Description |
|---|---|---|
| `type` | UInt8 | ID of the ILP Packet type |
| `data` | Variable-Length Octet String | Packet contents, prefixed with their length |

See the ASN.1 definition [here](../asn1/InterledgerPacket.asn).

#### ILP Prepare

ILP Prepare packets are `type` 12.

| Field | Type | Description |
|---|---|---|
| `amount` | UInt64 | Local amount, denominated in the minimum divisible unit of the asset of the bilateral relationship. This field is modified by each connector, who applies their exchange rate before forwarding the packet |
| `expiresAt` | Fixed-Length [Interledger Timestamp](../asn1/InterledgerTypes.asn) | Date and time when the packet expires. This field is modified by each connector, who subtracts some amount of time from the expiry before forwarding the packet |
| `executionCondition` | UInt256 | Sha256 hash digest of the `fulfillment` that will execute the transfer of value represented by this packet |
| `destination` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the receiver |
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data |

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

#### ILP Fulfill

ILP Fulfill packets are `type` 13.

| Field | Type | Description |
|---|---|---|
| `fulfillment` | UInt256 | 32-byte preimage of the `executionCondition` from the corresponding ILP Prepare packet | 
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data |

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

#### ILP Reject

ILP Reject packets are `type` 14.

| Field | Type | Description |
|---|---|---|
| `code` | 3-Character IA5String | [ILP Error Code](#error-codes) |
| `triggeredBy` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the party that created this error |
| `message` | UTF8 String | User-readable error message, primarily intended for debugging purposes |
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data |

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

### Error Codes

#### F__ - Final Error

Final errors indicate that the payment is invalid and should not be retried unless the details are changed.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **F00** | **Bad Request** | Generic sender error. | (empty) |
| **F01** | **Invalid Packet** | The ILP packet was syntactically invalid. | (empty) |
| **F02** | **Unreachable** | There was no way to forward the payment, because the destination ILP address was wrong or the connector does not have a route to the destination. | (empty) |
| **F03** | **Invalid Amount** | The amount is invalid, for example it contains more digits of precision than are available on the destination ledger or the amount is greater than the total amount of the given asset in existence. | (empty) |
| **F04** | **Insufficient Destination Amount** | The receiver deemed the amount insufficient, for example you tried to pay a $100 invoice with $10. | (empty) |
| **F05** | **Wrong Condition** | The receiver generated a different condition and cannot fulfill the payment. | (empty) |
| **F06** | **Unexpected Payment** | The receiver was not expecting a payment like this (the memo and destination address don't make sense in that combination, for example if the receiver does not understand the transport protocol used) | (empty) |
| **F07** | **Cannot Receive** | The receiver is unable to accept this payment due to a constraint. For example, the payment would put the receiver above its maximum account balance. | (empty) |
| **F99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |

#### T__ - Temporary Error

Temporary errors indicate a failure on the part of the receiver or an intermediary system that is unexpected or likely to be resolved soon. Senders SHOULD retry the same payment again, possibly after a short delay.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **T00** | **Internal Error** | A generic unexpected exception. This usually indicates a bug or unhandled error case. | (empty) |
| **T01** | **Ledger Unreachable** | The connector has a route or partial route to the destination but was unable to reach the next ledger. Try again later. | (empty) |
| **T02** | **Ledger Busy** | The ledger is rejecting requests due to overloading. Try again later. | (empty) |
| **T03** | **Connector Busy** | The connector is rejecting requests due to overloading. Try again later. | (empty) |
| **T04** | **Insufficient Liquidity** | The connector would like to fulfill your request, but it doesn't currently have enough money. Try again later. | (empty) |
| **T05** | **Rate Limited** | The sender is sending too many payments and is being rate-limited by a ledger or connector. If a connector gets this error because they are being rate-limited, they SHOULD retry the payment through a different route or respond to the sender with a `T03: Connector Busy` error. | (empty) |
| **T99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |

#### R__ - Relative Error

Relative errors indicate that the payment did not have enough of a margin in terms of money or time. However, it is impossible to tell whether the sender did not provide enough error margin or the path suddenly became too slow or illiquid. The sender MAY retry the payment with a larger safety margin.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **R00** | **Transfer Timed Out** | The transfer timed out, meaning the next party in the chain did not respond. This could be because you set your timeout too low or because something look longer than it should. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. | (empty) |
| **R01** | **Insufficient Source Amount** | Either the sender did not send enough money or the exchange rate changed before the payment was prepared. The sender MAY try again with a higher amount, but they SHOULD NOT do this indefinitely or a malicious connector could steal money from them. | (empty) |
| **R02** | **Insufficient Timeout** | The connector could not forward the payment, because the timeout was too low to subtract its safety margin. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. | (empty) |
| **R99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |
