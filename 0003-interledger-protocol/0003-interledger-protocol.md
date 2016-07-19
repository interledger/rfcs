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

Addresses are hierarchically structured strings consisting of segments delimited by the period (`.`) character.

```
g.us.bank1.bob
```

More information about ILP addresses can be found in the [ILP Address Specification](../0015-ilp-addresses/).

The mapping from addresses to local accounts on a ledger is defined by the ledger protocol.

### Connectors

Connectors implement the interledger protocol to forward payments between ledgers. Connectors also implement the [Connector to Connector Protocol (CCP)](../0010-connector-to-connector-protocol/) to coordinate routing and other interledger control information.

## Specification

### ILP Payment Format

Here is a summary of the fields in the ILP payment packet format:

| Field | Type | Short Description |
|:--|:--|:--|
| amount | UInt64 | Amount the destination account should receive, denominated in the asset of the destination ledger |
| account | Address | Address corresponding to the destination account |
| data | OCTET STRING | Transport layer data attached to the payment |

#### amount

    UInt64 ::= INTEGER (0..18446744073709551615)

Amount in discrete units of the receiving ledger's asset type. Note that the amount is counted in terms of the smallest indivisible unit on the receiving ledger.

#### account

    -- Readable names for special characters that may appear in ILP addresses
    hyphen IA5String ::= "-"
    period IA5String ::= "."
    underscore IA5String ::= "_"
    tilde IA5String ::= "~"

    -- A standard interledger address
    Address ::= IA5String
      (FROM
        ( hyphen
        | period
        | "0".."9"
        | "A".."Z"
        | underscore
        | "a".."z"
        | tilde )
      )
      (SIZE (1..1023))

[Interledger Address](../0015-ilp-addresses/) of the receiving account.

#### data

    OCTET STRING (SIZE(0..32767))

Arbitrary data that is attached to the payment. The contents are defined by the transport layer protocol.

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

| Header Type ID | Protocol | Message Type |
|:--|:--|:--|
| 1 | [ILP](#ilp-header-format) | IlpPayment |
| 2 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteLiquidityRequest |
| 3 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteLiquidityResponse |
| 4 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteBySourceAmountRequest |
| 5 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteBySourceAmountResponse |
| 6 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteByDestinationAmountRequest |
| 7 | [ILQP](../0008-interledger-quoting-protocol/) | QuoteByDestinationAmountResponse |
