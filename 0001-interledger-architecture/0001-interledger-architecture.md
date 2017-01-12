# Interledger Architecture

This document outlines the Interledger architecture and explains how the different layers relate to each other.

The Interledger architecture is heavily inspired by the Internet architecture described in [RFC 1122](https://tools.ietf.org/html/rfc1122), [RFC 1123](https://tools.ietf.org/html/rfc1123) and [RFC 1009](https://tools.ietf.org/html/rfc1009).

<span class="show alert alert-danger">**This is a strawman proposal.** Choices made in this document are merely intended as a starting point.</span>

## Introduction

This document is intended to provide an overview over the Interledger architecture and protocol suite.

## The Interledger Architecture

All electronic transfers have to be recorded in stateful systems. Otherwise the same instance of an asset could be sent to two different destinations, essentially duplicating the asset. This is also known as a double-spend. We call these stateful systems *ledgers*.

Ledgers consist of *accounts*. Accounts are individual buckets containing a decimal amount of one type of asset, usually (but not always) associated with an owner. This amount is also called the account's *balance*. Balances can be positive or negative, representing assets or liabilities.

Assets can be transferred between accounts on the same ledger. We call these events *book transfers* or just *transfers*.

A transfer of assets across ledgers requires two or more local book transfers. Some system must know the relationship between the two transfers. We call this system a *connector*. The same system may act as both a ledger and a connector.

The Interledger is a network of independent and diverse ledgers. Each account is part of a particular ledger; the Interledger itself is only conceptual.

### Architectural Assumptions

#### Ledgers contain only one type of asset.

We assume that all assets within one ledger are fungible. Within one ledger transfers can happen directly from sender to recipient and do not require a third party exchanger.

When a single organization such as a bank manages accounts in multiple different assets of different types, we treat each asset as belonging to its own ledger.

#### Connectors do not keep transfer state information.

Just as Internet gateways do not keep connection state information, connectors do not keep transfer state information. All state is kept at the ledger level and connectors merely react to and trigger ledger events.

Note that this does not mean that all connectors are necessarily stateless. They may keep track of their available liquidity or even maintain an internal ledger if they are transacting on behalf of third parties. But we are assuming that they do not keep authoritative state about transfers.

#### Routing complexity should be in the connectors.

Routing is a complex and difficult problem, and ought to be performed by the connectors, not the end users of the system. An important objective is to isolate user software from changes caused by the inevitable evolution of the Interledger routing architecture.

#### The system must tolerate wide ledger variation.

A basic objective of the Interledger design is to tolerate a wide range of ledger characteristics --- e.g. throughput, latency, fees, access restrictions, reliability, decentralization. In addition it must support all types of different asset characteristics --- e.g. divisibility, fungibility, interest/demurrage, issuance.

### Interledger Protocol Suite

The Interledger architecture is separated into four layers:

![Interledger architecture layers](assets/interledger-architecture-layers.png)


#### Application Layer

The application layer is the top layer of the Interledger protocol suite. Protocols on this layer are responsible for negotiating the key properties of a payment:

* Source Account
* Destination Account
* Amount
* Condition

Once these parameters are decided, the application layer protocol will instantiate a transport layer protocol to initiate the payment.

Application layer protocols include open protocols such as the Open Web Payment Scheme (OWPS) and proprietary protocols such as the Ripple Payment Services Protocol (RPSP).

#### Transport Layer

The transport layer provides end-to-end transaction services for applications. There are three primary transport layer protocols at the moment:

* Optimistic Transport Protocol (OTP)
* Universal Transport Protocol (UTP)
* Atomic Transport Protocol (ATP)

OTP is a trivial transport protocol which simply transfers funds without the protection of escrow. Hence it is only suitable for very small microtransactions where efficiency matters more than reliability.

UTP uses escrowed transfers to guarantee that no funds leave the sender's account unless the transaction was successfully completed. It is suitable for transactions of any size and should be considered the default choice.

ATP uses escrowed transfers and a set of pre-agreed, trusted notaries in order to guarantee atomicity across multiple ledgers. It is relatively expensive to set up, but can be used to reduce the need for reconciliation.

#### Interledger Layer

All Interledger transport protocols use the Interledger Protocol (ILP) to communicate with connectors about transfer requests. This may include requesting a quote or requesting a transfer on another ledger.

The Interledger layer defines a standard way to refer to ledgers, accounts and amounts. This is used in routing as well as to try and make quotes comparable.

#### Ledger Layer

In order to facilitate transfers between accounts, ledgers must implement some API or protocol. We call this the ledger layer. There is a wide variety of ledger layer protocols, corresponding to the many different types of ledger.

## Ledger Layer

### Introduction

Ledger protocols are responsible for executing the individual transfers that constitute an Interledger transaction. They are also used by connectors to communicate with each other. Ledger layer protocols can differ widely depending on the type of ledger. For example, a central ledger will likely use a very different protocol than a blockchain, but for interledger purposes they are both ledgers and may be accessed using the same primitive operations as defined in this architecture.

### Requirements

#### Minimal Support

For minimal Interledger support, the ledger MUST have the ability for funds to be transferred from one account to another. This enables OTP transactions to pass through this ledger. It also allows third parties to act as escrow providers in order to enable UTP and ATP transactions on the ledger.

#### Basic Support

For basic Interledger support, a ledger MUST fulfill the requirements for minimal support and also the following:

The ledger MUST provide cryptographic escrow. Escrow means that transfers can have four states:

![enter image description here](https://lh3.googleusercontent.com/-QHsehrPTXgM/Vu_zs1dLWPI/AAAAAAAAEys/zchHKJj_MQs/s0/Transfer%252520States.png "Transfer States")

* Proposed -- Nothing has happened yet.
* Prepared -- Funds are held in escrow.
* Executed -- The transfer has completed.
* Rejected -- The transfer has been canceled (and funds returned to the sender.)

<span class="show alert alert-info">**Hint:** Escrow is the financial equivalent of a [two-phase commit](http://foldoc.org/two-phase%20commit).</span>


The ledger MUST be able to verify a simple SHA-256 hashlock cryptographic escrow condition in order to automatically trigger the release of the escrow. It must also allow a timeout to automatically roll back an escrowed transfer.

The ledger MUST support attaching a short message or *memo* to each transfer.

#### Full Support

The ledger MUST fulfill the requirements for basic support and also the following:

It MUST support all cryptographic condition types with the status "recommended".

It MUST support memos to be added for the credited and debited accounts separately and SHOULD support fairly large memo sizes.

It MUST support a way to discover connectors connected to the ledger.

It MUST support a way to look up a fulfillment by condition hash. It SHOULD automatically reject new transfers (that have not been prepared yet) that have an execution condition for which the ledger already knows the fulfillment. This aids in [UTP error recovery](#error-recovery).

### Example Protocols

#### Simple Ledger Protocol (SLP)

Simple Ledger Protocol (SLP) is a RESTful, JSON-based protocol that was developed specifically to provide the minimum functionality required for full Interledger support.

A reference implementation of a ledger using SLP can be found [here](https://github.com/interledger/five-bells-ledger).

#### Blockchain Protocols (e.g. Bitcoin)

Blockchains are distributed, peer-to-peer systems that provide consensus over a single shared state. Any blockchain that supports escrowed funds transfers is in principle capable of acting as a ledger connected to the Interledger.

Bitcoin for instance supports multiple credits and debits as well as SHA-256 hashlocked escrow transfers which means it can participate in OTP/ILP and UTP/ILP Interledger transactions. Bitcoin's BIP-65 enhancement proposal provides the timeouts required for Basic level support.

#### Legacy Protocols (e.g. ACH, ISO 20022)

Legacy protocols often do not provide escrow functionality. In this case, the protocol can either be upgraded, or a highly trusted participant (e.g. a bank) can act as an escrow provider.

#### Proprietary Wallet Protocols (e.g. PayPal API)

There are large numbers of proprietary ledgers out there. This includes web-based and mobile wallets. These types of systems can usually be extended with cryptographic escrow functionality by their operator in order to connect them to the Interledger.

#### Other Proprietary Protocols (e.g. Skype API)

Some proprietary protocols intentionally do not provide general ledger functionality. A common example are stored-value systems, such as gift cards, loyalty points or pre-paid accounts. Such systems can still be connected to the Interledger in a limited capacity. For example a pre-paid account ledger could be set up to act as a receiving ledger, but not as a sending or intermediate ledger.

By creating two classes of users -- resellers and end users -- and only allowing transfers if the sender is a reseller and the recipient is a user, merchants can create Interledger-capable ledgers which behave like stored-value systems. Such systems allow deposits, but do not allow withdrawals.

## Interledger Layer

### Introduction

The Interledger Protocol (ILP) ensures that different connectors are interoperable and can work together to route transactions.

### Protocols

#### Interledger Protocol (ILP)

When initiating an Interledger transaction, the sender will make a transfer to a connector using their local Ledger layer protocol. Within this transfer, the sender will include an [ILP Packet](../0003-interledger-protocol/) which tells the receiving connector the final destination, the amount to be transferred and -- if applicable -- the condition.

Note that the exact method of transmitting this data packet is dependent on the ledger layer protocol. Typically, it will be included in the transfer in a memo field. However, some ledgers may specify a different method for transporting the ILP packet.

#### Interledger Quoting Protocol (ILQP)

Before an Interledger transfer takes place, the sender will request quotes from connectors which are connected to the same ledger. These quote requests happen via the [Interledger Quoting Protocol (ILQP)](../0008-interledger-quoting-protocol/).

Senders MAY cache quotes and send repeated transfers through the same connector.

#### Interledger Control Protocol (ILCP)

The Interledger Control Protocol (ILCP) is a protocol used by connectors to exchange routing information and communicate payment errors.

**TODO**: add link

## Transport Layer

### Introduction

Transport layer protocols are responsible for coordinating the different transfers that make up an Interledger transaction. The safety guarantees afforded to the participants of a transaction vary depending on the type of transport protocol used.

### Protocols

#### Optimistic Transport Protocol (OTP)

The Optimistic Transport Protocol (OTP) is the trivial case of a transport protocol. It simply makes a transfer to the next connector. The connector may or may not make the requested transfer and the sender is out the money either way.

For most cases, OTP will not be appropriate. However, it may make sense in the case of recurring microtransactions where a few lost transactions are not a big deal.

<span class="show alert alert-warning">**TODO:** Need to figure out how OTP can detect dropped transfers and adjust the route accordingly.</span>

#### Universal Transport Protocol (UTP)

The Universal Transport Protocol (UTP) is the standard and recommended transport protocol. It sets up a cascading chain of escrowed transfers in order to ensure delivery of funds.

The protocol flow is described in the [Interledger whitepaper](https://interledger.org/interledger.pdf).

##### Error Recovery

A UTP execution chain can be interrupted if a connector fails to deliver the condition fulfillment. In that case the sender will think that the transaction failed and retry it. While retrying, some connector will try to create a prepared transfer on a ledger which already knows the corresponding fulfillment, which will cause the request to fail. The connector will notice this and simply pass back the fulfillment without paying anything.

In other words, the failed connector will lose money and some other connector will win money, but from the sender and recipient's point of view everything has executed normally.

#### Atomic Transport Protocol (ATP)

The Atomic Transport Protocol (ATP) is the most conservative, but also most complex of the standard Interledger transport protocols. In addition to the ledgers and connectors, it also involves a set of impartial notaries, which must be agreed upon by the sender, recipient and connectors involved in the transaction.

Since each party chooses their own set of notaries to trust, there may not be any overlap and ATP could not be used in that case. Notaries may be selected using an automatic process or preselected by a group with standing agreements among the participants.

The protocol flow is described in the [Interledger whitepaper](https://interledger.org/interledger.pdf).

##### As a Sub-Protocol

ATP can be used as a sub-protocol for part of a UTP transaction. This happens when a connector decides to create an ATP transfer as the next hop. It takes on both the risk of being unable to pass on the receipt and the risk of the notaries failing. This makes sense to do if the next connector quotes a better price for an ATP transfer than for a UTP transfer.

Similarly, an ATP transaction can turn into a UTP transaction when a connector decides to use UTP for the next hop. It takes on the risk of not being able to pass on the receipt to the notaries. This makes sense if ATP is not available.

## Application Layer

### Introduction

Application layer protocols deal with the exchange of payment details and associated negotiation.

### Simple Payment Setup Protocol (SPSP)

The Simple Payment Setup Protocol (SPSP) is an application layer protocol for negotiating payment details. SPSP handles account and amount discovery, condition creation, quoting and setup. SPSP uses Webfinger ([RFC 7033](https://tools.ietf.org/html/rfc7033)) and an HTTP-based protocol for querying account and amount details, [ILQP](#interledger-quoting-protocol-ilqp) for quoting, and [UTP](#universal-transport-protocol-utp) for payment execution.

The protocol is described in [IL-RFC 9](../0009-simple-payment-setup-protocol/).

### Defining Other Application Layer Protocols

Creators of other application layer protocols should consider the following:

1. Account discovery
2. Amount and condition communication
3. Additional details communicated in memo
4. Condition types supported or required
5. Transport protocol
6. Incoming payment validation (amount, condition, etc.)
