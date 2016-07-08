---
coding: utf-8

title: The Interledger Protocol
docname: draft-thomas-interledger-01
category: info

pi: [toc, sortrefs, symrefs, comments]
smart_quotes: off

area: security
author:
  -
    ins: S. Thomas
    name: Stefan Thomas
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: stefan@ripple.com
    uri: http://www.ripple.com
  -
    ins: E. Schwartz
    name: Evan Schwartz
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: evan@ripple.com
    uri: http://www.ripple.com
  -
    ins: A. Hope-Bailie
    name: Adrian Hope-Bailie
    org: Ripple
    street: 300 Montgomery Street
    city: San Francisco
    region: CA
    code: 94104
    country: US
    phone: -----------------
    email: adrian@ripple.com
    uri: http://www.ripple.com

normative:
    RFC3447:
    RFC4648:
    draft-thomas-crypto-conditions-01:

informative:
    RFC2119:
    RFC3110:
    RFC4871:
    RFC791:

--- note_Feedback

This specification is a part of the [Interledger Project](https://interledger.org/) work. Feedback related to this specification should be sent to <public-interledger@w3.org>.

--- abstract

This document specifies the Standard Interledger Protocol (ILP). It draws heavily from the definition of the Internet Protocol (IP) defined in [RFC 791](https://tools.ietf.org/html/rfc791). The interledger protocol is the culmination of more than a decade of research in decentralized payment protocols. This work was started in 2004 by Ryan Fugger, augmented by the development of Bitcoin in 2008 and has involved numerous contributors since then.

--- middle

# Introduction {#intro}

Transferring digital assets betwen two accounts on a single ledger or within the confines of a constrained payment network requires no specific orchestration or protocol. In contrast, a transfer of digital assets from an account on one ledger to an account on an entirely different ledger requires at least one counter-party to transfer the assets between ledgers and also a well defined protocol for orchestration of the steps required to complete the transaction atomically and protect all participants from counter-party risk.

The interledger protocol provides for transmitting payments from source accounts to destination accounts on different ledgers, where source accounts and destination accounts are identified by variable length, hierarchically structured universal addresses.

The protocol defines a universal account addressing scheme that allows a payment to be routed to any account on any ledger connected to the Interledger and a mechanism to protect the sender and receiver from risk such that the sender will either hold irrefutable proof that the receiver got their payment or will receive a complete reversal of their initial transfer. 

## Scope {#scope}

The interledger protocol is intentionally limited in scope to provide the functions necessary to deliver a payment from a source account to a destination account over an interconnected system of ledgers. There are no mechanisms to augment end-to-end payment reliability, liquidity management, identity, or other services commonly found in payment protocols. The interledger protocol can capitalize on the services of its supporting ledgers to provide various types and qualities of service.

## Definitions {#definitions}

##### Transfer
&emsp;Change in ownership of some asset

##### Ledger
&emsp;System which records transfers

##### Connector
&emsp;System which relays transfers between two ledgers

##### Payment
&emsp;An exchange of assets involving one or more transfers on different ledgers

## Basic Concepts {#concepts}

On the Interledger there are two roles. A ledger is a system of accounts, with balances, and the role of the ledger is to record transfers which change the balances of the accounts on the ledger. A connector is an entity holding a balance on two or more ledgers. Connectors trade a debit against their balance on one ledger for a credit against their balance on another as a means of facilitating the payment between the two ledgers.

## Operation {#operation}

The central function of the interledger protocol is to provide addressing across different ledgers.

Each host sending and receiving interledger payments has an interledger module that uses the addresses in the interledger header to transmit interledger payments toward their destinations. Interledger modules share common rules for interpreting addresses. The modules (especially in connectors) also have procedures for making routing decisions and other functions.

The interledger protocol treats each interledger payment as an independent entity unrelated to any other interledger payment. There are no connections or channels (virtual or otherwise).

Interledger payments do not carry a dedicated time-to-live or remaining-hops field. Instead, the amount field acts as an implicit time-to-live: Each time the payment is forwarded, the forwarding connector will take some fee out of the inbound amount. Once a connector recognizes that the inbound amount is worth less (though not necessarily numerically smaller) than the destination amount in the Interledger header, it will refuse to forward the payment.

# Overview {#overview}

## Relation to Other Protocols {#protocols}

The interledger protocol interfaces on one side to the higher level end-to-end protocols and on the other side to the local ledger protocol. In this context a "ledger" may be a small ledger owned by an individual or organization or a large public ledger such as Bitcoin.

## Model of Operation {#model}

The model of operation for transmitting funds from one application to another is illustrated by the following scenario:

> We suppose the source and destination hold accounts on different ledgers connected by a single connector.

> The sending application chooses an amount and calls on its local interledger module to send that amount as a payment and passes the destination address and other parameters as arguments of the call.

> The interledger module prepares an ILP header and attaches the data to it. The interledger module determines a destination account on the local ledger for this interledger address. In this case it is the account of a connector.

> It passes the chosen amount and the local destination account to the local ledger interface.

> The local ledger interface creates a local ledger transfer, then authorizes this transfer on the local ledger.

> The transfer arrives at a connector host via the local ledger interface. The local ledger interface extracts the ILP header and turns it over to the connector's interledger module. The interledger module determines from the interledger address that the payment is to be forwarded to another account in a second ledger. The interledger module converts the amount according to its locally available liquidity and determines the local account on the other ledger corresponding to the destination host. It calls on the local ledger interface for the destination ledger to send the transfer.

> This local ledger interface creates a local ledger transfer and authorizes it.

> At the destination host the ILP header is extracted by the local ledger interface and handed to the interledger module.

> The interledger module determines that the payment is for an application in this host. It passes the data to the application, passing the source address and other parameters as results of the call.

    Application                                          Application
           \                                                /
      Interledger Module   Interledger Module   Interledger Module
              \                 /       \                /
              LLI-1          LLI-1      LLI-2         LLI-2
                 \           /             \          /
                 Local Ledger 1           Local Ledger 2

## Function Description {#function}

The purpose of the interledger protocol is to enable hosts to route payments through an interconnected set of ledgers. This is done by passing the payments from one interledger module to another until the destination is reached. The interledger modules reside in hosts and connectors in the interledger system. The payments are routed from one interledger module to another through individual ledgers based on the interpretation of an interledger address. Thus, the central component of the interledger protocol is the interledger address.

When routing payments with relatively large amounts, the connectors and the intermediary ledgers they choose in the routing process may not be trusted. The sending application MAY use the [hold](#holds-and-payment-reliability) mechanism provided by underlying ledgers to protect the sender and receivers from this risk by providing a condition in the ILP header that will be fulfilled by the receiver when the they receive the payment.

### Addressing {#addressing}

As with the [internet protocol](https://tools.ietf.org/html/rfc791#section-2.3), interledger distinguishes between names, addresses, and routes.
> "A name indicates what we seek. An address indicates where it is. A route indicates how to get there. The internet protocol deals primarily with addresses. It is the task of higher level (i.e., end-to-end or application) protocols to make the mapping from names to addresses."

The interledger module translates interledger addresses to local ledger addresses. Connectors and local ledger interfaces are responsible for translating addresses into interledger routes and local routes, respectively.

Addresses are hierarchically structured strings consisting of segments delimited by the slash (`.`) character. In order to distinguish the present address format from future or alternative versions, the protocol prefix `ilp:` MUST be used:

```
ilp:us.bank1.bob
```

Care must be taken in mapping interledger addresses to local ledger accounts. Examples of address mappings may be found in "Address Mappings" ((TODO)).

### Connectors {#addressing}

Connectors implement the interledger protocol to forward payments between ledgers. Connectors also implement other protocols to coordinate routing and other interledger control information.

## Specification {#specification}

### ILP Header Format {#ilp-header}

Here is a summary of the fields in the ILP header format:

| Field | Type | Short Description |
|:--|:--|:--|
| version | INTEGER(0..255) | ILP protocol version (currently `1`) |
| destinationAddress | IlpAddress | Address corresponding to the destination account |
| destinationAmount | IlpAmount | Amount the destination account should receive, denominated in the asset of the destination ledger |
| condition | OCTET STRING | See [draft-thomas-crypto-conditions-01](#draft-thomas-crypto-conditions-01). The condition may be included in the packet or may be transmitted through the ledger layer. |
| expiresAt | IlpTimestamp | Maximum expiry time of the last transfer that the recipient will accept |

#### version
<code>INTEGER(0..255)</code>

The version of the Interledger Protocol being used. This document describes version `1`.

#### destinationAddress
<code>IlpAddress :== SEQUENCE OF OCTET STRING</code>

Hierarchical routing label.

#### destinationAmount
<code>IlpAmount :== SEQUENCE { mantissa INTEGER, exponent INTEGER(-128..127) }</code>

Base 10 encoded amount.

#### condition
<code>???</code>

???

#### expiresAt
<code>???</code>

???

## Holds and Payment Reliability {#holds}

Interledger payments may be transmitted through connectors and intermediary ledgers that are not trusted by the sender or receiver. If connectors fail to pass on payments, money could be lost.

Ledgers MAY provide transfer hold functionality to protect hosts from the risk posed by others in a payment route. Protocols on top of the interledger protocol MAY take advantage of this capability to provide reliable payments by specifying a value in the condition field of the ILP header.

Transfers with holds occur in two steps rather than one. In the first step, the sending account's balance is debited. The transfer is then called "prepared". Each hold is associated with a condition that releases the hold. Conditions SHOULD be provided in the Crypto-Conditions format. The second step occurs when the condition is fulfilled and the funds are then released (credited) to the recipient.

Held transfers may also have an expiry date. If the transfer is on hold at the time it expires, the funds will be returned to the sender. If the transfer has already been fully executed, the expiry date has no effect.

Not all ledgers support held transfers. In the case of a ledger that doesn't, the sender and recipient of the local ledger transfer MAY choose a commonly trusted party to carry out the hold functions. There are three options:

1. The sender MAY trust the receiver. The sender will perform a regular transfer in the first step and the receiver will perform a transfer back if the condition has not been met in time.

2. The receiver MAY trust the sender. The sender will notify the receiver about the intent to transfer. If the receiver provides a fulfillment for the condition before the expiry date, the sender will perform a regular transfer to the receiver.

3. The sender and receiver MAY appoint a mutually trusted third-party which has an account on the local ledger. The sender performs a regular transfer into a neutral third-party account. In the first step, funds are transfered into the account belonging to the neutral third-party.
