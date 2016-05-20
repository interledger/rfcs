# Interledger Protocol

## Preface

This document specifies the Standard Interledger Protocol. It draws heavily from RFC 791. The interledger protocol is the culmination of the work started in 2004 by Ryan Fugger towards the creation of a decentralized peer-to-peer payment protocol. There have been many contributors to this work both in terms of concepts and in terms of text. This edition simplifies

## Introduction

### Motivation

The Interledger Protocol is designed for use in interconnected systems of digital asset ledgers with transfer capability. The interledger protocol provides for transmitting payments from sources to destinations, where sources and destinations are hosts identified by variable length addresses. The interledger protocol also provides for payment channels, if necessary, for transmission through non-scalable ledgers.

### Scope

The interledger protocol is specifically limited in scope to provide the functions necessary to deliver a payment from a source to a destination over an interconnected system of ledgers. There are no mechanisms to augment end-to-end payment reliability, liquidity management, identity, or other services commonly found in payment protocols. The interledger protocol can capitalize on the services of its supporting ledgers to provide various types and qualities of service.

### Interfaces

This protocol is called on by host-to-host payment protocols in an interledger environment. This protocol calls on local ledger protocols to carry the interledger payment to the next connector or destination account.

For example, a Universal Transport Protocol (UTP) module would call on the interledger module to take a UTP memo (including the UTP header and user data) as the data portion of an interledger payment. The UTP module would provide the address and other parameters in the interledger header to the interledger module as arguments of the call. The interledger module would then create an interledger payment and call on the local ledger interface to transmit the interledger payment.

In the Ripple case, for example, the interledger module would call on a local ledger module which would add the Ripple envelope to the interledger payment creating a Ripple transaction to transmit to the Ripple Consensus Ledger. The Ripple address would be derived from the interledger address by the local ledger interface and would be the address of some account in the Ripple network, that account might belong to a connector to other ledgers.

### Operation

The interledger protocol implements one basic function: addressing.

The interledger modules use the addresses carried in the interledger header to transmit interledger payments toward their destinations. The selection of a path for transmission is called routing.

The model of operation is that an interledger module resides in each host engaged in interledger communication and in each connector that interconnects ledgers. These modules share common rules for interpreting address fields. In addition, these modules (especially in connectors) have procedures for making routing decisions and other functions.

The interledger protocol treats each interledger payment as an independent entity unrelated to any other interledger payment. There are no connections or channels (virtual or otherwise).

The interledger protocol uses one key mechanism in providing its service: Amount

The Amount acts as an implicit time-to-live: Each time the payment is forwarded, the forwarding connector will take some fee out of the inbound amount. Once a connector recognizes that the inbound amount is worth less (though not necessarily numerically smaller) than the destination amount in the ILP header, it will refuse to forward the packet.

### Definitions

##### Ledger
&emsp;System which records transfers

##### Connector
&emsp;System which relays transfers between two ledgers

##### Transfer
&emsp;Local book transfer affecting two or more accounts on a single ledger

##### Payment
&emsp;An exchange of assets involving one or more transfers on different ledgers

## Overview

### Relation to Other Protocols

The following diagram illustrates the place of the interledger protocol in the protocol hierarchy:

![Interledger model](https://lh3.googleusercontent.com/-aEwlmiKtjNA/Vu_2bJmbQeI/AAAAAAAAEy4/sAIT_zXRi2g/s0/Interledger%252520Architecture%252520Layers.png "Interledger Architecture Layers")

Interledger protocol interfaces on one side to the higher level end-to-end protocols and on the other side to the local ledger protocol.  In this context a "ledger" may be a small ledger owned by an individual or organization or a large public ledger such as Bitcoin.

### Model of Operation

The model of operation for transmitting funds from one application program to another is illustrated by the following scenario:

> We suppose that this payment will involve one intermediate connector.

> The sending application program chooses an amount and calls on its local interledger module to send that amount as a payment and passes the destination address and other parameters as arguments of the call.

> The interledger module prepares an ILP header and attaches the data to it. The interledger module determines a destination account on the local ledger for this interledger address, in this case it is the account of a connector.

> It passes the chosen amount and the local destination account to the local ledger interface.

> The local ledger interface creates a local ledger transfer, then authorizes this transfer on the local ledger.

> The transfer arrives at a connector host via the local ledger interface. The local ledger interface extracts the ILP header and turns it over to the interledger module. The interledger module determines from the interledger address that the payment is to be forwarded to another account in a second ledger. The interledger module converts the amount according to its locally available liquidity and determines the local ledger account corresponding to the destination host. It calls on the local ledger interface for that ledger to send the transfer.

> This local ledger interface creates a local ledger transfer and authorizes it.

> At the destination host the ILP header is extracted by the local ledger interface and handed to the interledger module.

> The interledger module determines that the payment is for an application program in this host. It passes the data to the application program, passing the source address and other parameters as results of the call.

    Application                                           Application
    Program                                                   Program
          \                                                   /
      Interledger Module   Interledger Module   Interledger Module
              \                 /       \                /
              LLI-1          LLI-1      LLI-2         LLI-2
                 \           /             \          /
                 Local Ledger 1           Local Ledger 2

### Function Description

The function or purpose of Internet Protocol is to move payments through an interconnected set of ledgers. This is done by passing the payments from one interledger module to another until the destination is reached. The interledger modules reside in hosts and connectors in the interledger system. The payments are routed from one interledger module to another through individual ledgers based on the interpretation of an interledger address.  Thus, one important mechanism of the interledger protocol is the interledger address.

When routing payments with large amounts, the connectors and the intermediary ledgers they choose in the process of routing may not be trusted. To protect the sender and receiver from this risk, an hold mechanism is provided in the interledger protocol.

#### Addressing

A distinction is made between names, addresses, and routes [4]. A name indicates what we seek. An address indicates where it is. A route indicates how to get there. The interledger protocol deals primarily with addresses. It is the task of higher level (i.e., end-to-end or application) protocols to make the mapping from names to addresses. The interledger module maps interledger addresses to local net addresses. It is the task of lower level (i.e., local net or connectors) procedures to make the mapping from local net addresses to routes.

Addresses are hierarchically structured strings consisting of segments delimited by the slash (`/`) character. In order to distinguish the present address format from future or alternative versions, the protocol prefix `ilp:` MUST be used:

```
ilp:us/bank1/bob
```

Multiple addresses may be provided as different ways that the same destination can be reached. This provides a way to upgrade the addressing scheme in the future such that the new address and the old address can be provided within the same payment. It also allows recipients to provide multiple descriptions of where their account is located such that connectors can choose the one that is easiest and cheapest to reach.

Care must be taken in mapping interledger addresses to local ledger accounts. Examples of address mappings may be found in "Address Mappings" ((TODO)).

<!--
#### Hold

A transfer with hold occurs in two steps rather than one. In the first step, the sending account's balance is debited. The transfer is then called on-hold. Each hold is associated with a condition that releases the hold. Conditions are provided in a format described in ((TODO: Link to cc spec)). The second step occurs when the condition is fulfilled and the funds are then released (credited) to the recipient.

Held transfers may also have an expiry date. If the transfer is on hold at the time it expires, the funds will be returned to the sender. If the transfer has already been fully executed, the expiry date has no effect.

Not all ledgers support held transfers. In the case of a ledger that doesn't, the sender and recipient of the local ledger transfer should choose a commonly trusted party. There are three options:

1. The sender may trust the receiver. The sender will perform a regular transfer in the first step and the receiver will perform a transfer back if the condition has not been met in time.

2. The receiver may trust the sender. The sender will notify the receiver about the intent to transfer. If the receiver provides a fulfillment for the condition before the expiry date, the sender will perform a regular transfer to the receiver.

3. The sender and receiver may appoint a mutually trusted third-party which has an account on the local ledger. The sender performs a regular transfer into a neutral third-party account. In the first step, funds are transfered into the account belonging to the neutral third-party.
-->

#### Payment Channels

### Connectors

Connectors implement interledger protocol to forward payments between ledgers. Connectors also implement the Connector to Connector Protocol (CCP) to coordinate routing and other interledger control information.

In a connector the higher level protocols need not be implemented and the CCP functions are added to the ILP module.

    +-----------------------------------+
    | Interledger Protocol & ILQP & CCP |
    +-----------------------------------+
             |                 |
    +----------------+ +----------------+
    |  Local Ledger  | |  Local Ledger  |
    +----------------+ +----------------+

## Specification

### ILP Header Format

Here is a summary of the fields in the ILP header format:

| Field | Type | Short Description |
|:-|:-|:-|
| version | INTEGER | `1` |
| destinationAddress | IlpAddress | Address corresponding to the destination account. |
| destinationAmount | IlpAmount | Amount the destination account should receive, denominated in the asset of the destination ledger |
| nextHeader | INTEGER | Type of the next header. |

**TODO**: should we have the `sourceAddress` for sending error messages back?


<!--
| source | IlpAddress | Address corresponding to the source account. |
| destinationPrepareBy | IlpTimestamp | Time by which the final transfer should be prepared, otherwise the recipient may not attempt to fulfill the condition |
| condition | OCTET STRING | See the [condition spec](https://interledger.org/five-bells-condition/spec.html). The condition may be included in the packet or may be transmitted through the ledger layer. |
| data | OCTET STRING | Message or other data to be delivered to the destination account along with the payment (i.e. destination credit memo) |
| expiresAt | IlpTimestamp | Maximum expiry time of the last transfer that the recipient will accept |
-->


## Discussion

### Payment Channels
