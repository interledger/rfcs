# Interledger Architecture

This document outlines the Interledger architecture and explains how the different layers relate to each other. The [Interledger Protocol (ILP)](#interledger-protocol-ilp) is one layer in the Interledger architecture.

The Interledger architecture is heavily inspired by the Internet architecture described in [RFC 1122](https://tools.ietf.org/html/rfc1122), [RFC 1123](https://tools.ietf.org/html/rfc1123) and [RFC 1009](https://tools.ietf.org/html/rfc1009).

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

![Interledger architecture layers](../shared/graphs/interledger-model.svg)


#### Application Layer

The application layer is the top layer of the Interledger protocol suite. Protocols on this layer are responsible for negotiating the key properties of a payment:

* Source Account
* Destination Account
* Destination Amount

Once these parameters are decided, the application layer protocol will instantiate a transport layer protocol to initiate the payment.

An example of an application layer protocol is the [Simple Payment Setup Protocol (SPSP)](#simple-payment-setup-protocol-spsp).

#### Transport Layer

The transport layer is responsible for two things:

* Generating the condition
* Encoding (e.g. encrypting) the application layer data

There are currently two transport layer protocols:

* [Pre-Shared Key (PSK)](#pre-shared-key-psk)

    The sender and recipient agree upon a secret key in advance. The sender uses this key to generate the condition and encrypt the application data. The recipient uses the same key to generate the fulfillment and decrypt the application data.

* [Interledger Payment Request (IPR)](#interledger-payment-request-ipr)

    The recipient generates the condition during the quoting phase, and the sender cannot know the fulfillment until the recipient uses it to execute the payment. This is useful for building non-repudiable application layer protocols.

#### Interledger Layer

All Interledger transport protocols use the [Interledger Protocol (ILP)](#interledger-protocol-ilp) to communicate with connectors about transfer requests. This may include requesting a quote or requesting a transfer on another ledger.

The Interledger layer defines a standard way to refer to ledgers, accounts and amounts. This is used in routing as well as to try and make quotes comparable.

#### Ledger Layer

In order to facilitate transfers between accounts, ledgers must implement some API or protocol. This is called the ledger layer. There is a wide variety of ledger layer protocols, corresponding to the many different types of ledger.

## Ledger Layer Requirements

### Introduction

Ledger protocols are responsible for executing the individual transfers that constitute an Interledger transaction. They are also used by connectors to communicate with each other. Ledger layer protocols can differ widely depending on the type of ledger. For example, a central ledger will likely use a very different protocol than a blockchain, but for interledger purposes they are both ledgers and may be accessed using the same primitive operations as defined in this architecture.

### Requirements

#### Minimal Support

For minimal Interledger support, a ledger MUST have the ability to transfer funds from one account to another. All additional functionality can be implemented in a separate "adapter" service. To use ILP in that case, users of the ledger must also trust the adapter. For further details, see [Appendix A](#appendix-a-holds-without-native-ledger-support).

#### Basic Support

For basic Interledger support, a ledger MUST fulfill the requirements for minimal support and also the following:

The ledger MUST provide authorization holds, conditional upon a cryptographic hash and timeout as described below. During an authorization hold, money is put aside for a specific transfer until that transfer's outcome has been decided.

Transfers using authorization holds can be in four distinct states:

![Transfers start in the proposed state, transition to the prepared state and finally to the executed state, which is final. Proposed and prepared transfers can also transition to the rejected state, which is final as well.](../shared/graphs/transfer-states.svg)

* Proposed -- Nothing has happened yet.
* Prepared -- Funds are held.
* Executed -- The transfer has completed.
* Rejected -- The transfer has been canceled (and funds returned to the sender.)

<span class="show alert alert-info">**Hint:** Authorization holds are the financial equivalent of a [two-phase commit](http://foldoc.org/two-phase%20commit).</span>

The ledger MUST be able to release the held funds to the receiver upon receiving a 32-byte preimage whose SHA-256 hash matches a value provided by the sender. The ledger MUST accept ONLY 32 byte preimages or support specifying the fulfillment length when the transfer is prepared.

The ledger MUST support releasing held funds back to the sender after a timeout.

The ledger MUST support attaching a short message or *memo* to each transfer.

The ledger MUST support notifications to account holders when transfers are prepared, executed, or rejected that affect their accounts.

#### Full Support

The ledger MUST fulfill the requirements for basic support and also the following:

The ledger MUST support memos up to 65535 bytes.

The ledger MUST support sending an authenticated message of up to 65535 bytes to the holder of another account on the ledger.

The ledger MUST support a way to look up a fulfillment by condition hash. It SHOULD automatically reject new transfers (that have not been prepared yet) that have an execution condition for which the ledger already knows the fulfillment. This aids in [error recovery](#error-recovery).

The ledger MUST support preparing, executing, and rejecting transfers in 1 second or less.

The ledger MUST define an [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) prefix and scheme such that accounts on the ledger can be addressed using canonical ILP addresses.

### Example Protocols

#### Five Bells Ledger Protocol (5BLP)

Five Bells Ledger Protocol (5BLP) is a RESTful, JSON-based protocol that was developed specifically to provide the minimum functionality required for full Interledger support.

A reference implementation of a ledger using 5BLP can be found [here](https://github.com/interledger/five-bells-ledger).

#### Blockchain Protocols (e.g. Bitcoin)

Blockchains are distributed, peer-to-peer systems that provide consensus over a single shared state. Any blockchain that supports escrowed funds transfers is in principle capable of acting as a ledger connected to the Interledger.

For example, Bitcoin supports SHA-256 hashlocked escrow transfers which means it can participate in ILP Interledger transactions. Bitcoin's [BIP-65](https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki) proposal provided the timeouts required for Basic level support.

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

The protocol is specified in [IL-RFC 3](../0003-interledger-protocol/0003-interledger-protocol.md) and the flow is described in the [Interledger whitepaper](https://interledger.org/interledger.pdf).

<span class="show alert alert-info">**Note:** Interledger only supports Universal mode as described in the whitepaper. Atomic mode can be used by adjacent subsets of participants in an Interledger payment if desired, however this is not part of the standard.</span>

##### Error Recovery

An ILP execution chain can be interrupted if a connector fails to deliver the condition fulfillment. In this case, the sender thinks the transaction failed and retries it using the same condition as the original transaction. At some point during the retry, a connector inevitably prepares a transfer on a ledger which already knows the corresponding fulfillment. (This may be the recipient's ledger or a ledger before it in the chain.) When this happens, the ledger fails the transfer and provides the fulfillment to the connector which prepared it. This connector can pass the fulfillment back up the chain to receive money without sending any.

In other words, the failed connector loses money and some other connector gains money, but from the sender and the recipient's perspective everything has executed normally.

#### Interledger Quoting Protocol (ILQP)

Before an Interledger payment occurs, the sender requests quotes from connectors which are connected to the same ledger as the sender. The sender and the connector use the [Interledger Quoting Protocol](../0008-interledger-quoting-protocol/) to communicate these quotes.

Senders MAY cache quotes and send repeated transfers through the same connector.

## Transport Layer

### Introduction

Transport layer protocols used by the senders and receivers of Interledger payments to determine the payment condition and other details. The guarantees afforded to the sender vary depending on the type of transport protocol used.

### Protocols

#### Pre-Shared Key (PSK)

The Pre-Shared Key (PSK) protocol is an end-to-end protocol in which the sender and receiver use a shared secret to generate the payment condition, authenticate the ILP packet, and encrypt application data. Using PSK, the sender is guaranteed that fulfillment of their transfer indicates the receiver got the payment, provided that no one aside from the sender and receiver have the secret and the sender did not submit the fulfillment. PSK is recommended for most use cases.

The protocol is specified in [IL-RFC 16](../0016-pre-shared-key/0016-pre-shared-key.md).

#### Interledger Payment Request (IPR)

The Interledger Payment Request (IPR) protocol is an end-to-end protocol in which the receiver generates the payment details and condition. In IPR, the sender does not share the secret used to generate the condition and fulfillment with the sender or anyone else, but the sender must ask the recipient to generate and share a condition before sending each payment. IPR is primarily useful for building non-repudiable application layer protocols, in which the sender's posession of the fulfillment proves to third parties that the sender has paid the receiver for a specific obligation.

The protocol is specified in [IL-RFC 11](../0011-interledger-payment-request/0011-interledger-payment-request.md).

## Application Layer

### Introduction

Application layer protocols deal with the exchange of payment details and associated negotiation.

### Simple Payment Setup Protocol (SPSP)

The Simple Payment Setup Protocol (SPSP) is an application layer protocol for negotiating payment details. SPSP handles account and amount discovery, condition creation, quoting and setup. SPSP uses Webfinger ([RFC 7033](https://tools.ietf.org/html/rfc7033)) and an HTTP-based protocol for querying account and amount details, [ILQP](#interledger-quoting-protocol-ilqp) for quoting, and [ILP](#interledger-protocol-ilp) for payment execution.

The protocol is described in [IL-RFC 9](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).

### Defining Other Application Layer Protocols

Creators of other application layer protocols should consider the following:

1. Account discovery
2. Amount and condition negotiation and communication
3. Additional details communicated in ILP packet data
4. Transport protocol

## Appendix A: Holds Without Native Ledger Support

Not all ledgers support held transfers. In the case of a ledger that doesn't, the sender and recipient of the local ledger transfer MAY choose a commonly trusted party to carry out the hold functions. There are three options:

1. The sender MAY trust the receiver. The sender will perform a regular transfer in the first step and the receiver will perform a transfer back if the condition has not been met in time.

2. The receiver MAY trust the sender. The sender will notify the receiver about the intent to transfer. If the receiver provides a fulfillment for the condition before the expiry date, the sender will perform a regular transfer to the receiver.

3. The sender and receiver MAY appoint a mutually trusted third-party which has an account on the local ledger. The sender performs a regular transfer into a neutral third-party account. In the first step, funds are transfered into the account belonging to the neutral third-party.

