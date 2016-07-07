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

##### Transfer
&emsp;Change in ownership of some asset

##### Ledger
&emsp;System which records transfers

##### Connector
&emsp;System which relays transfers between two ledgers

##### Payment
&emsp;An exchange of assets involving one or more transfers on different ledgers

## Overview

### Relation to Other Protocols

The following diagram illustrates the place of the interledger protocol in the protocol hierarchy:

![Interledger model](../0001-interledger-architecture/assets/interledger-architecture-layers.png)

The interledger protocol interfaces on one side to the higher level end-to-end protocols and on the other side to the local ledger protocol. In this context a "ledger" may be a small ledger owned by an individual or organization or a large public ledger such as Bitcoin.

### Model of Operation

#### Without Holds ("Optimistic Mode")

The protocol MAY be used without the security provided by holds -- sometimes referred to as "Optimistic Mode". The model of operation for transmitting funds from one application to another without holds is illustrated by the following scenario:

We suppose the source and destination have accounts on different ledgers connected by a single connector.

        (1)                                               (11)
    Application                                       Application
           \                                              /
           (2)                    (6)                  (10)
    Interledger Module    Interledger Module    Interledger Module
              \               /       \                /
               (3)          (5)       (7)            (9)
              LLI-1       LLI-1      LLI-2         LLI-2
                 \   (4)   /             \    (8)   /
              Local Ledger 1           Local Ledger 2

1. The sending application chooses an amount and calls on its local interledger module to send that amount as a payment and passes the destination address and other parameters as arguments of the call.

2. The interledger module prepares an ILP packet and attaches the data to it. The interledger module determines a destination account on the local ledger for this interledger address. In this case it is the account of a connector. It passes the chosen amount and the local destination account to the local ledger interface.

3. The local ledger interface creates a local ledger transfer, then authorizes this transfer on the local ledger.

4. The ledger executes the transfer and notifies the connector.

5. The connector host's local ledger interface receives the notification and passes it to the interledger module.

6. The connector's interledger module extracts the ILP packet from the notification and determines from the interledger address that the payment is to be forwarded to another account in a second ledger. The interledger module converts the amount according to its locally available liquidity and determines the local account on the other ledger corresponding to the destination host. It calls on the local ledger interface for the destination ledger to send the transfer, which includes the same ILP packet.

7. This local ledger interface creates a local ledger transfer and authorizes it.

8. The ledger executes the transfer and notifies the destination host.

9. The destination host's local ledger interface receives the notification and passes it to the interledger module.

10. The interledger module extracts the ILP packet and determines that the payment is for an application in this host. It passes the transfer data to the application.

11. The destination application receives the notification of incoming funds and reacts accordingly.

#### With Holds ("Universal Mode")

The protocol MAY be used with transfer holds to ensure a sender's funds are delivered to the destination or returned to the sender's account. The model of operation is illustrated with the following example:

      (1,21)                                               (11)
    Application                                        Application
           \                                               /
         (2,20)                 (6,16)                 (10,12)
    Interledger Module    Interledger Module    Interledger Module
              \               /       \                 /
             (3,19)       (5,17)     (7,15)         (9,13)
              LLI-1       LLI-1       LLI-2         LLI-2
                 \  (4,18) /             \  (8,14)   /
              Local Ledger 1           Local Ledger 2


1. The sending application uses a higher-level protocol to negotiate the address, an amount, and a cryptographic condition with the destination. It calls on the interledger module to send a payment with these parameters.

2. The interledger module prepares the ILP packet, chooses the account to send the local ledger transfer to, and passes them to the local ledger interface.

3. The local ledger interface creates a local ledger transfer, including the crytographic condition, then authorizes this transfer on the local ledger.

4. The ledger puts the sender's funds on hold -- it does not transfer the funds to the connector -- and notifies the connector.

5. The connector host's local ledger interface receives the notification and passes it to the interledger module.

6. The connector's interledger module extracts the ILP packet and determines that it should forward the payment. The interledger module calls on the destination ledger's local ledger interface to send the second transfer, including the same condition as the sender's transfer.

7. The local ledger interface creates a local ledger transfer, including the crytographic condition, then authorizes this transfer on the local ledger.

8. The ledger puts the connector's funds on hold -- it does not transfer the funds to the destination -- and notifies the destination host.

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

Addresses are hierarchically structured strings consisting of segments delimited by the period (`.`) character. In order to distinguish the present address format from future or alternative versions, the protocol prefix `ilp:` MUST be used:

```
ilp:us.bank1.bob
```

Care must be taken in mapping interledger addresses to local ledger accounts. Examples of address mappings may be found in "Address Mappings" ((TODO)).

### Connectors

Connectors implement the interledger protocol to forward payments between ledgers. Connectors also implement the [Connector to Connector Protocol (CCP)](../0010-connector-to-connector-protocol/) to coordinate routing and other interledger control information.

![Interledger is an overlay across ledgers](assets/ilp-ledger-relation.png)

## Specification

### ILP Header Format

Here is a summary of the fields in the ILP header format:

| Field | Type | Short Description |
|:--|:--|:--|
| version | INTEGER(0..255) | ILP protocol version (currently `1`) |
| destinationAddress | IlpAddress | Address corresponding to the destination account |
| destinationAmount | IlpAmount | Amount the destination account should receive, denominated in the asset of the destination ledger |
| nextHeader | INTEGER(0..65535) | Type of the next header |

**TODO**: should we have the `sourceAddress` for sending error messages back?


<!--
| source | IlpAddress | Address corresponding to the source account. |
| destinationPrepareBy | IlpTimestamp | Time by which the final transfer should be prepared, otherwise the recipient may not attempt to fulfill the condition |
| condition | OCTET STRING | See the [condition spec](https://interledger.org/five-bells-condition/spec.html). The condition may be included in the packet or may be transmitted through the ledger layer. |
| data | OCTET STRING | Message or other data to be delivered to the destination account along with the payment (i.e. destination credit memo) |
| expiresAt | IlpTimestamp | Maximum expiry time of the last transfer that the recipient will accept |
-->

#### version
<code>INTEGER(0..255)</code>

The version of the Interledger Protocol being used. This document describes version `1`.

#### destinationAddress
<code>IlpAddress :== SEQUENCE OF OCTET STRING</code>

Hierarchical routing label.

#### destinationAmount
<code>IlpAmount :== SEQUENCE { mantissa INTEGER, exponent INTEGER(-128..127) }</code>

Base 10 encoded amount.

**TODO**: Are we going to regret the base-10 encoding?

#### nextHeader
<code>INTEGER(0..65535)</code>

Type of the next header.

Header types include optional interledger extension headers, such as the [Source Routing Header](#source-routing-header-format) and transport protocols, such as [Optimistics Transport Protocol (OTP)](../0005-optimistic-transport-protocol/).

The list of headers is terminated by the special value `0xffff`, i.e. all bits set. When a ledger module finishes processing a header containing this value as its `nextHeader`, it MUST stop parsing and forward all remaining bytes without modification.

When an interledger module encounters an unknown header type, it MUST act according to the value of the two most significant bits:

| Bits | Meaning |
|:--|:--|
| 00 | Drop the payment, reply with an error, issue a refund if possible |
| 01 | Drop the payment, reply with an error, do not issue a refund |
| 10 | Drop the payment quietly, do not reply |
| 11 | Ignore the header, process the payment as if the header wasn't there |

The list of header types is managed by IANA, please see [Header Type Registry](#header-type-registry).

### Generic Extension Header Format

Here is a description of the format that all headers (except the ILP header) MUST follow:

| Field | Type | Short Description |
|:--|:--|:--|
| nextHeader | INTEGER | Type of the next header |
| size | INTEGER | Size of this header in octets |

#### nextHeader
<code>INTEGER(0..65535)</code>

See [`nextHeader`](#nextheader).

#### size
<code>INTEGER(0..65535)</code>

Total size of the header in bytes, including the generic header fields.

### Memo Locator Header Format

This header indicates where in the payload (remaining data after the headers) the user memo can be found. If this header is not provided, the interledger module MUST assume that the entire payload is the user memo. All interledger modules MUST support this header type.

This header is provided for forward compatibility. Future extensions to the protocol may need to carry more data than can fit in a 64KB header. This header allows them to re-map the location of the user data in the payload and add their own content to the payload. By supporting this header from the start, we ensure that this functionality will be backwards compatible with all ILP implementations.

| Field | Type | Short Description |
|:--|:--|:--|
| nextHeader | INTEGER | Type of the next header |
| size | INTEGER | Size of this header in octets |
| memoPosition | INTEGER | Starting position of the memo |
| memoSize | INTEGER | Size of the memo in octets |

#### memoPosition
<code>INTEGER(0..4294967295)</code>

Starting position of the memo. Interledger modules MUST start reading the memo this many octets after the start of the payload.

If `memoPosition` is greater than the payload size, interledger modules SHOULD drop the payment.

#### memoSize
<code>INTEGER(0..4294967295)</code>

Size of the memo in octets.

If `memoPosition + memoSize` is greater than the payload size, interledger modules SHOULD drop the payment.

### Hop-by-hop Header Format

This header may be used for source routing.

**TODO**: Document format.

## Discussion

### Holds Without Native Ledger Support

Not all ledgers support held transfers. In the case of a ledger that doesn't, the sender and recipient of the local ledger transfer MAY choose a commonly trusted party to carry out the hold functions. There are three options:

1. The sender MAY trust the receiver. The sender will perform a regular transfer in the first step and the receiver will perform a transfer back if the condition has not been met in time.

2. The receiver MAY trust the sender. The sender will notify the receiver about the intent to transfer. If the receiver provides a fulfillment for the condition before the expiry date, the sender will perform a regular transfer to the receiver.

3. The sender and receiver MAY appoint a mutually trusted third-party which has an account on the local ledger. The sender performs a regular transfer into a neutral third-party account. In the first step, funds are transfered into the account belonging to the neutral third-party.
### Payment Channels

## Appendix A: ASN.1 Module

## Appendix B: IANA Considerations

### Header Type Registry

The following initial entries should be added to the Interledger Header Type registry to be created and maintained at (the suggested URI) http://www.iana.org/assignments/interledger-header-types:

| Header Type ID | Description |
|:--|:--|
| 0 | [Interledger Protocol (ILP)](#ilp-header-format) |
| 1 | [Optimistic Transport Protocol (OTP)](../0005-optimistic-transport-protocol/) |
| 2 | [Universal Transport Protocol (UTP)](../0006-universal-transport-protocol/) |
| 3 | [Atomic Transport Protocol (ATP)](../0007-atomic-transport-protocol/) |
| 4 | [Interledger Quoting Protocol (ILQP)](../0008-interledger-quoting-protocol/) |
