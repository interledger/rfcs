# Interledger Protocol (ILP)

## Preface

This document specifies the Interledger Protocol (ILP). It draws heavily from the definition of the Internet Protocol (IP) defined in [RFC 791](https://tools.ietf.org/html/rfc791). The interledger protocol is the culmination of more than a decade of research in decentralized payment protocols. This work was started in 2004 by Ryan Fugger, augmented by the development of Bitcoin in 2008 and has involved numerous contributors since then.

## Introduction

### Motivation

Payment networks today are siloed and disconnected. Payments are relatively easy within one country or if the sender and recipient have accounts on the same network or ledger. However, sending from one ledger to another is often impossible. Where connections do exist, they are manual, slow, or expensive.

The Interledger Protocol provides for routing payments across different digital asset ledgers while isolating senders and receivers from the risk of intermediary failures. Secure multi-hop payments and automatic routing enables a global network of networks for different types of value that can connect any sender with any receiver.

### Scope

The interledger protocol is intentionally limited in scope to provide the functions necessary to deliver a payment from a source to a destination over an interconnected system of ledgers. It includes minimal requirements for underlying ledgers and it does not include public key infrastructure, identity, liquidity management, or other services commonly found in payment protocols.

### Interfaces

This protocol is called on by hosts through higher level protocol modules in an interledger environment. Interledger protocol modules call on local ledger protocols to carry the interledger payment to the next connector or destination account.

For example, a [`Simple Payment Setup Protocol (SPSP)`](../0009-simple-payment-setup-protocol/) module would call the interledger module with the address and other parameters in the interledger packet to send a payment. The interledger module would send a transfer to the next connector or destination account along with the interledger packet and according to the parameters given. The transfer and interledger packet would be received by the next host's interledger module and handled by each each successive connector and finally the destination's SPSP module.

In the Ripple case, for example, the interledger module would call on a local ledger module which would create a Ripple transaction with the interledger packet attached to transmit to the Ripple Consensus Ledger. The Ripple address would be derived from the interledger address by the local ledger interface and would be the address of some account in the Ripple network, which might belong to a connector to other ledgers.

### Operation

The central functions of the interledger protocol are addressing hosts and securing payments across different ledgers.

Each host sending and receiving interledger payments has an interledger module that uses the addresses in the interledger header to transmit interledger payments toward their destinations. Interledger modules share common rules for interpreting addresses. The modules (especially in connectors) also have procedures for making routing decisions and other functions.

The interledger protocol uses transfer holds to ensure that senders' funds are either delivered to the destination account or returned to the sender's account. This mechanism is described in greater detail in the [Overview](#overview) and the [Interledger Whitepaper](https://interledger.org/interledger.pdf).

The interledger protocol treats each interledger payment as an independent entity unrelated to any other interledger payment. There are no connections or channels (virtual or otherwise).

Interledger payments do not carry a dedicated time-to-live or remaining-hops field. Instead, the amount field acts as an implicit time-to-live: Each time the payment is forwarded, the forwarding connector will take some fee out of the inbound amount. Once a connector recognizes that the inbound amount is worth less (though not necessarily numerically smaller) than the destination amount in the ILP header, it will refuse to forward the payment.

### Definitions

- **Transfer:** A zero-sum set of balance changes that causes the change in ownership of some asset.
- **Ledger:** A system which records transfers.
- **Account:** A balance of one asset in a ledger, with an owner and metadata.
- **Payment:** A series of transfers that delivers money from a sender to a receiver, possibly in different ledgers.
- **Sender:** The originator of a payment. This is the entity whose account is ultimately debited.
- **Receiver:** The beneficiary of a payment. This is the entity whose account is ultimately credited.
- **Connector:** An entity and system which relays a payment across ledgers by participating in two transfers. The connector's account is credited in one ledger and debited in another ledger.
- **Destination Ledger:** The ledger where the receiver's account is.


## Overview

### Relation to Other Protocols

The following diagram illustrates the place of the interledger protocol in the protocol hierarchy:

![Interledger model](../shared/graphs/interledger-model.svg)

The interledger protocol interfaces on one side to the higher level end-to-end protocols and on the other side to the local ledger protocol. In this context a "ledger" may be a small ledger owned by an individual or organization or a large public ledger such as Bitcoin.

### Model of Operation

The protocol uses transfer holds to ensure a sender's funds are delivered to the destination or returned to the sender's account. The model of operation is illustrated with the following example:

      (1,21)                                               (11)
    Application                                        Application
           \                                               /
         (2,20)                 (6,16)                 (10,12)
    Interledger Module    Interledger Module    Interledger Module
              \               /       \                 /
             (3,19)       (5,17)     (7,15)         (9,13)
              LLI-1       LLI-1       LLI-2         LLI-2
                 \  (4,18) /             \  (8,14)   /
                Local Ledger 1          Local Ledger 2


1. The sending application uses a higher-level protocol to negotiate the address, an amount, and a cryptographic condition with the destination. It calls on the interledger module to send a payment with these parameters.

2. The interledger module prepares the ILP packet, chooses the account to send the local ledger transfer to, and passes them to the local ledger interface.

3. The local ledger interface creates a local ledger transfer, including the crytographic condition, then authorizes this transfer on the local ledger.

4. The ledger puts the sender's funds on hold—it does not transfer the funds to the connector—and notifies the connector.

5. The connector host's local ledger interface receives the notification and passes it to the interledger module.

6. The connector's interledger module extracts the ILP packet and determines that it should forward the payment. The interledger module calls on the destination ledger's local ledger interface to send the second transfer, including the same condition as the sender's transfer.

7. The local ledger interface creates a local ledger transfer, including the crytographic condition, then authorizes this transfer on the local ledger.

8. The ledger puts the connector's funds on hold—it does not transfer the funds to the destination—and notifies the destination host.

9. The destination host's local ledger interface receives the notification and passes it to the interledger module.

10. The interledger module extracts the ILP packet and determines that the payment is for an application in this host. It passes the transfer data to the application.

11. The destination application receives the notification and recognizes that funds are on hold pending the condition fulfillment. It checks the details of the incoming transfer against what was agreed upon with the sender. If checks pass, the application produces the condition fulfillment and passes it to the interledger module.

12. The destination's interledger module passes the fulfillment to the local ledger interface.

13. The local ledger interface submits the fulfillment to the ledger.

14. The destination ledger validates the fulfillment against the held transfer's condition. If the fulfillment is valid and the transfer is not expired, the ledger executes the transfer and notifies the destination host and the connector.

15. The connector's local ledger interface receives the fulfillment notification and passes it to the interledger module.

16. The connector's interledger module receives the fulfillment and passes it to the local ledger interface corresponding to the source ledger.

17. This ledger interface submits the fulfillment to the source ledger.

18. The source ledger validates the fulfillment against the held transfer's condition. If the fulfillment is valid and the transfer is not expired, the ledger executes the transfer and notifies the connector and the sender's host.

19. The sender's local ledger interface receives the fulfillment notification and passes it to the interledger module.

20. The sender's interledger module receives the fulfillment notification and passes it to the application.

21. The sender's application receives the fulfillment notification and reacts accordingly.

### Function Description

The purpose of the interledger protocol is to enable hosts to route payments through an interconnected set of ledgers. This is done by passing the payments from one interledger module to another until the destination is reached. The interledger modules reside in hosts and connectors in the interledger system. The payments are routed from one interledger module to another through individual ledgers based on the interpretation of an interledger address. Thus, a central component of the interledger protocol is the interledger address.

When routing payments with relatively large amounts, the connectors and the intermediary ledgers they choose in the routing process may not be trusted. Holds provided by underlying ledgers MAY be used to protect the sender and receivers from this risk. In this case, the ILP packet contains a cryptographic condition and expiration date.

#### Addressing

As with the [internet protocol](https://tools.ietf.org/html/rfc791#section-2.3), interledger distinguishes between names, addresses, and routes.
> "A name indicates what we seek. An address indicates where it is. A route indicates how to get there. The internet protocol deals primarily with addresses. It is the task of higher level (i.e., end-to-end or application) protocols to make the mapping from names to addresses."

The interledger module translates interledger addresses to local ledger addresses. Connectors and local ledger interfaces are responsible for translating addresses into interledger routes and local routes, respectively.

Addresses are hierarchically structured strings consisting of segments delimited by the period (`.`) character.

```
g.us.bank1.bob
```

More information about ILP addresses can be found in the [ILP Address Specification](../0015-ilp-addresses/).

The mapping from addresses to local accounts on a ledger is defined by the ledger protocol.

### Connectors

Connectors implement the interledger protocol to forward payments between ledgers and relay errors back along the path.

Connectors also implement the [Connector to Connector Protocol (CCP)](../0010-connector-to-connector-protocol/) to coordinate routing and other interledger control information.

### Packet

The ILP Packet is the core data structure of the interledger protocol. The ILP Packet is attached to each transfer in the Interledger payment, so the recipient of the transfer can confirm the reason for the transfer.

The ILP Packet has two major consumers, who use it differently:

- Connectors use the [ILP Address][] contained in the packet to route the payment.
- The receiver of the payment uses the packet to identify the packet and which condition to fulfill.

[ILP Address]: ../0015-ilp-addresses/0015-ilp-addresses.md


#### Relation to ILQP Packets

The [Interledger Quoting Protocol](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md) is another protocol that exists in the Interledger layer of the Interledger protocol suite. (For more information, see [Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md).) ILP Packets share a type space with ILQP Packets, to avoid ambiguity in case the wrong packet is attached to a transfer or other message.

The type value `1` indicates an ILP Packet. The type values `2` through `7` indicate ILQP Packets.

#### Life-Cycle of the ILP Packet

The exact use of the ILP Packet depends on the transport protocol you use. In [IPR][], the receiver generates and communicates the packet to the sender. In [PSK][], the sender generates the packet according to agreed-upon rules with a pre-shared secret.
[IPR]: ../0011-interledger-payment-request/0011-interledger-payment-request.md

When the sender prepares a transfer to start the payment, the sender attaches the ILP Packet to the transfer, in the memo field if possible. If a ledger does not support attaching the entire ILP Packet to a transfer as a memo, users of that ledger can transmit the ILP Packet using another system, but MUST be able to correlate transfers and ILP Packets. ***Rome's note: Doesn't this also have some sort of trust implications, like the system for correlating transfers must be trusted to the same extent as the ledger because it could be used to steal money if it's malicious?***

When a connector sees an incoming prepared transfer with an ILP Packet, the connector reads the ILP Packet to get the ILP Address of the payment's receiver. If the connector has a route to the receiver's account, the connector prepares a transfer to continue the payment, and attaches the same ILP Packet to the new transfer.

When the receiver sees the incoming prepared transfer, the receiver reads the ILP Packet to confirm the details of the packet. The receiver confirms that the amount from the ILP Packet matches the amount actually delivered by the transfer. The receiver decodes the data of the ILP Packet and matches the condition to the packet. (Depending on the transport protocol, the packet's data MAY contain the condition.) The receiver MUST confirm the integrity of the ILP Packet, for example with a [hash-based message authentication code (HMAC)](https://en.wikipedia.org/wiki/Hash-based_message_authentication_code). If the receiver finds the transfer acceptable, the receiver releases the fulfillment for the transfer, which can be used to execute all the prepared transfers.


### Errors

Errors may be generated at any point as an Interledger payment is being prepared or by the receiver. Connectors that are notified of an outgoing transfer being rejected MUST reject the corresponding incoming transfer with the same error.

Connectors SHOULD include their ILP address in the [`forwardedBy`](#forwardedby) field in the error. Connectors SHOULD NOT modify errors
in any other way.

See below for the [ILP Error Format](#ilp-error-format) and [ILP Error Codes](#ilp-error-codes).



## Specification

### ILP Packet


The ILP Packet is represented as binary data. In addition to being faster to transmit and encode/decode, the binary format of the packet gives it a canonical format so it can be hashed consistently. The formal definition of the ILP Packet is the [ASN.1 Interledger Protocol module](../asn1/InterledgerProtocol.asn). The ILP Packet consists of the following data, in order:

| Field     | Type            | Description                                    |
|:----------|:----------------|:-----------------------------------------------|
| `type`    | UInt8           | The value `1` indicates this is an ILP Packet (`InterledgerProtocolPaymentMessage`). See [Relation to ILQP Packets](#relation-to-ilqp-packets) below. |
| `amount`  | UInt64          | The amount to deliver, in discrete units of the destination ledger's asset type. The scale of the units is determined by the destination ledger's smallest indivisible unit. |
| `account` | [ILP Address][] | The ILP address of the account where the receiver should ultimately receive the payment. Represented with a subset of ASCII characters. Length-prefixed, up to 1023 bytes. |
| `data`    | Octet String    | Arbitrary data for the receiver. Length-prefixed, up to 32767 bytes. This data is set by the transport layer of the payment. (For example, this may contain [PSK Headers][PSK].) |

[PSK]: ../0016-pre-shared-key/0016-pre-shared-key.md

### Holds Without Native Ledger Support

Not all ledgers support held transfers. In the case of a ledger that doesn't, the sender and recipient of the local ledger transfer MAY choose a commonly trusted party to carry out the hold functions. There are three options:

1. The sender MAY trust the receiver. The sender will perform a regular transfer in the first step and the receiver will perform a transfer back if the condition has not been met in time.

2. The receiver MAY trust the sender. The sender will notify the receiver about the intent to transfer. If the receiver provides a fulfillment for the condition before the expiry date, the sender will perform a regular transfer to the receiver.

3. The sender and receiver MAY appoint a mutually trusted third-party which has an account on the local ledger. The sender performs a regular transfer into a neutral third-party account. In the first step, funds are transfered into the account belonging to the neutral third-party.

### ILP Error Format

Here is a summary of the fields in the ILP error format:

| Field | Type | Short Description |
|:--|:--|:--|
| code | IA5String | [ILP Error Code](#ilp-error-codes)
| triggeredBy | Address | ILP address of the entity that originally emitted the error |
| forwardedBy | SEQUENCE OF Address | ILP addresses of connectors that relayed the error message |
| triggeredAt | Timestamp | Time when the error was initially emitted |
| data | OCTET STRING | Error data provided for debugging purposes |

#### code

    IA5String (SIZE(3))

See [ILP Error Codes](#ilp-error-codes) for the list of error codes and their meanings.

#### triggeredBy

[ILP Address](#account) of the entity that originally emitted the error.

#### forwardedBy

[ILP Addresses](#account) of the connectors that relayed the error message.

#### triggeredAt

    Timestamp ::= GeneralizedTime

Date and time when the error was initially emitted.

#### data

    OCTET STRING (SIZE(0..8192))

Error data provided for debugging purposes. Protocols built on top of ILP SHOULD specify the encoding format of error `data`.

### ILP Error Codes

Inspired by [HTTP Status Codes](https://tools.ietf.org/html/rfc2616#section-10), ILP errors are categorized based on the intended behavior of the caller when they get the given error.

#### S__ - Sender Error

Sender errors indicate that the payment is invalid and should not be retried unless the details are changed.

| Code | Name | Description |
|---|---|---|
| **S00** | **Bad Request** | Generic sender error. |
| **S01** | **Invalid Packet** | The ILP packet was syntactically invalid. |
| **S02** | **Unreachable** | There was no way to forward the payment, because the destination ILP address was wrong or the connector does not have a route to the destination. |
| **S03** | **Invalid Amount** | The amount is invalid, for example it contains more digits of precision than are available on the destination ledger or the amount is greater than the total amount of the given asset in existence. |
| **S04** | **Insufficient Destination Amount** | The receiver deemed the amount insufficient, for example you tried to pay a $100 invoice with $10. |
| **S05** | **Wrong Condition** | The receiver generated a different condition and cannot fulfill the payment. |
| **S06** | **Unexpected Payment** | The receiver was not expecting a payment like this (the memo and destination address don't make sense in that combination, for example if the receiver does not understand the transport protocol used) |
| **S07** | **Cannot Receive** | The receiver is unable to accept this payment due to a constraint. For example, the payment would put the receiver above its maximum account balance. |
| **S99** | **Application Error** | Reserved for application layer protocols. |

#### T__ - Temporary Error

Temporary errors indicate a failure on the part of the receiver or an intermediary system that is unexpected or likely to be resolved soon. Senders SHOULD retry the same payment again, possibly after a short delay.

| Code | Name | Description |
|---|---|---|
| **T00** | **Internal Error** | A generic unexpected exception. This usually indicates a bug or unhandled error case. |
| **T01** | **Ledger Unreachable** | The connector has a route or partial route to the destination but was unable to reach the next ledger. Try again later. |
| **T02** | **Ledger Busy** | The ledger is rejecting requests due to overloading. Try again later. |
| **T03** | **Connector Busy** | The connector is rejecting requests due to overloading. Try again later. |
| **T04** | **Insufficient Liquidity** | The connector would like to fulfill your request, but it doesn't currently have enough money. Try again later. |
| **T05** | **Rate Limited** | The sender is sending too many payments and is being rate-limited by a ledger or connector. |
| **T99** | **Application Error** | Reserved for application layer protocols. |

#### R__ - Relative Error

Relative errors indicate that the payment did not have enough of a margin in terms of money or time. However, it is impossible to tell whether the sender did not provide enough error margin or the path suddenly became too slow or illiquid. The sender MAY retry the payment with a larger safety margin.

| Code | Name | Description
|---|---|---|
| **R01** | **Transfer Timed Out** | The transfer timed out, i.e. the next party in the chain did not respond. This could be because you set your timeout too low or because something look longer than it should. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. |
| **R02** | **Insufficient Source Amount** | Either you didn't send enough money or there wasn't enough liquidity. The sender MAY try again with a higher amount, but they SHOULD NOT do this indefinitely or a malicious connector could steal money from them. |
| **R03** | **Insufficient Timeout** | The connector could not forward the payment, because the timeout was too low to subtract its safety margin. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. |
| **R99** | **Application Error** | Reserved for application layer protocols. |

### Payment Channels

## Appendix A: ASN.1 Module

## Appendix B: IANA Considerations

### Header Type Registry

The following initial entries should be added to the Interledger Header Type registry to be created and maintained at (the suggested URI) http://www.iana.org/assignments/interledger-header-types:

| Header Type ID | Protocol | Message Type |
|:--|:--|:--|
| 1 | [ILP](#ilp-header-format) | IlpPayment |
| 2 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteLiquidityRequest |
| 3 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteLiquidityResponse |
| 4 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteBySourceAmountRequest |
| 5 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteBySourceAmountResponse |
| 6 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteByDestinationAmountRequest |
| 7 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteByDestinationAmountResponse |
