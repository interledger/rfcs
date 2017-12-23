---
title: Interledger Architecture
draft: 2
---
# Interledger Architecture

Interledger provides for secure payments across multiple assets on different ledgers. The architecture consists of a conceptual model for interledger payments, a mechanism for securing payments, and a suite of protocols that implement this design.

The [Interledger Protocol (ILP)](#interledger-layer) is the core of the Interledger protocol suite.

Colloquially the whole Interledger stack is sometimes referred to as "ILP". Technically, however, the Interledger Protocol is only one layer in the stack.

The Interledger architecture is heavily inspired by the Internet architecture described in [RFC 1122](https://tools.ietf.org/html/rfc1122), [RFC 1123](https://tools.ietf.org/html/rfc1123) and [RFC 1009](https://tools.ietf.org/html/rfc1009).

## Interledger Model

![Interledger Model: Sender, Connectors, Ledgers, Receiver](../shared/graphs/interledger-model.svg)

### Ledgers

*Ledgers* are stateful systems that track the ownership of *assets*. Ledgers contain buckets of assets known as *accounts* and record *transfers* between them. Each account has a *balance*, which is the amount of the ledger's assets the account holds. Account balances may be positive or negative, representing assets or liabilities.

**In the Interledger model, a ledger only tracks a single asset, which may be a currency, stock, commodity, etc.** One entity that maintains accounts denominated in multiple assets is described as having multiple ledgers.

A ledger may be operated by a single entity, as in the case of a bank, or it may be decentralized, as in the case of a blockchain or distributed ledger.

### Connectors

A *connector* is a system that facilitates *payments* across different ledgers. Connectors generate revenue from Interledger payments while accepting some risk.

In the Interledger model, connectors are described as separate logical systems even though the same entity may operate a ledger and a connector.

A connector receives a local transfer on one ledger in exchange for making another local transfer on a different ledger. A single interledger payment may include multiple connectors and may traverse any number of ledgers.

If the ledgers represent different assets, the connectors set the exchange rate between the transfers. Connectors may generate revenue from the difference in value between incoming and outgoing transfers. Senders may request quotes from multiple connectors to determine the best price before sending a payment.

Connectors *peer* with one another to exchange information used to determine the best route for a payment.

**Interledger ensures that senders' funds are safe throughout an multi-hop payment and cannot be stolen by faulty or malicious connectors (see [Interledger Security](#interledger-security)).**

### The Interledger

The Interledger protocol suite may be used to transact across any ledgers and connectors, whether they are public or private. There is no single network that all parties must connect to to use these protocols.

"The Interledger" is a conceptual network made up of independent and diverse ledgers linked by connectors. Each account "on the Interledger" is part of a particular ledger, but they may transact with others by sending interledger payments through different ledgers and connectors. Like "the Internet", the Interledger is not a single network but is comprised of multiple interconnected networks.

## Interledger Security

**Interledger uses *conditional transfers* to secure payments across multiple hops and even through untrusted connectors.** Senders are guaranteed cryptographic proof that the receiver got the payment or their money back, no matter how many ledgers and connectors are in between. Connectors take some risk, but this risk can be managed and is primarily based upon the connector's chosen ledgers and direct peers.

<span class="show alert alert-info">**Hint:** Conditional transfers or *authorization holds* are the financial equivalent of a [two-phase commit](http://foldoc.org/two-phase%20commit).</span>

### Conditional Transfers

Each local transfer is first *prepared* and then either *executed* or *rejected*. When a transfer is prepared, the funds of the source account are put on hold with a *cryptographic condition* and *timeout*. If the condition is fulfilled before the timeout, the transfer is executed and the funds are transferred. If the timeout is reached, the transfer expires and the the funds are returned to the source account automatically.

Inspired by the [Lightning Network](http://lightning.network), Interledger uses the digest of the [SHA-256](https://en.wikipedia.org/wiki/SHA-2) hash function as the condition for transfers. The fulfillment is a valid 32-byte preimage for the hash specified when the transfer was prepared. Ledgers are responsible for validating fulfillments. [Transport Layer](#transport-layer) protocols are used by the sender and receiver to generate the condition for a particular payment.

Conditional transfers are implemented at the [Clearing Layer](#clearing-layer) and may or may not be implemented by the underlying ledgers. See [IL-RFC 22: Hashed Timelock Agreements (HTLAs)](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md) for a full description of the different implementations of conditional transfers.

### Payment Flow

In Interledger payments, all component transfers are prepared before any are executed. No funds are transferred, so none can be lost if a connector fails or attempts to redirect the payment.

When the *receiver* is notified of funds on hold for them, they submit the *fulfillment* of the cryptographic condition to claim their funds. Each connector uses the same fulfillment to claim their incoming transfer.

The timeout of each successive transfer is shorter than the previous one, giving each connector a window of time to deliver the fulfillment even if their outgoing transfer was executed at the last possible moment.

For more details on the flow, see the [Interledger Protocol specification](../0003-interledger-protocol/0003-interledger-protocol.md) and the [Interledger whitepaper](https://interledger.org/interledger.pdf).

<span class="show alert alert-info">**Note:** Interledger only supports Universal mode as described in the whitepaper. Atomic mode can be used by adjacent subsets of participants in an Interledger payment if desired, but this is not part of the standard.</span>

### Connector Risk and Mitigation

Interledger connectors accept some risk in exchange for the revenue they generate from facilitating payments. In the Interledger payment flow, connectors' outgoing transfers are executed before their incoming transfers. After each connector is notified that the outgoing transfer has been executed, they have a window of time to deliver the fulfillment and execute the incoming transfer. Connectors that fail to deliver the fulfillment in time may lose money.

If some transfers in an Interledger payment are executed and others expire, the receiver will think the payment was completed but the sender may think the whole payment failed. Senders MAY retry payments that expire. If they do, they SHOULD use the same condition as the original payment. If the second attempt takes the same route, the connector that failed the first time can complete the payment by submitting the fulfillment without sending another outgoing transfer. Connectors should prefer senders (or aggregators of senders such as wallet services) and connectors that retry payments through the same route, because they increase the likelihood of completing such payments. Connectors may incentivize this behavior by offering better rates to parties known to retry failed payments through the same route.

Failing to deliver the fulfillment in time is the main risk connectors face and there are a number of additional strategies connectors should employ to mitigate and manage this risk. For more details, see [IL-RFC 18](../0018-connector-risk-mitigations/0018-connector-risk-mitigations.md).

## Interledger Protocol Suite

The Interledger stack is separated into the following layers:

![Interledger Protocol Suite](../shared/graphs/protocol-suite.svg)

**Note:** What was formerly known as the "Ledger Layer" is now split into the Settlement and Clearing Layers.

### Settlement Layer

In order for two parties to transact, they must be able to send and receive value in the same settlement system. Examples of settlement systems include bank ledgers, closed-loop payment networks, cryptocurrencies, blockchains, or cash.

Settlement systems may or may not have APIs, and the features that they support determine the type of clearing systems that can be used with them.

### Clearing Layer

It is often too slow or expensive to settle every payment via the underlying settlement system. In these cases, a clearing protocol may be used on top of the underlying settlement mechanism. Clearing protocols may be implemented on bilateral or multilateral bases, such as a trustline or a payment channel network like the [Lightning Network](https://lightning.network), respectively.

The Interledger Clearing Layer may be different from traditional clearing systems because it implements Conditional Transfers, also known as Hashed Timelock Agreements (HTLAs).

The most common types of Clearing Layer protocols are [payment channels](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md#simple-payment-channels) and [trustlines](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md#trustlines). See [IL-RFC 22: Hashed Timelock Agreements (HTLAs)](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md) for more details about different types of clearing protocols.

**Note:** Real-Time Gross Settlement may be used instead of a separate Clearing Layer if the underlying settlement system is sufficiently fast, inexpensive, and has sufficient throughput.

Most implementations of Interledger use a plugin architecture to abstract the differences between different Clearing and Settlement Layers. For an example of this, see [IL-RFC 4](../0004-ledger-plugin-interface/0004-ledger-plugin-interface.md), which defines the interface for the Javascript implementation.

### Interledger Layer

The Interledger layer is responsible for relaying payments across multiple clearing systems. It is comprised of two key components that are used together: the Interledger Protocol (ILP) and the Interledger Quoting Protocol (ILQP).

The [Interledger Protocol (ILP)](../0003-interledger-protocol/0003-interledger-protocol.md) is the core of the Interledger stack and defines standard address and packet formats that instruct connectors where to send a payment.

[Interledger Addresses](../0015-ilp-addresses/0015-ilp-addresses.md) provide a ledger-agnostic way to address ledgers and accounts. Interledger addresses are dot-separated strings that contain prefixes to group ledgers. An example address might look like:
`g.us.acmebank.acmecorp.sales.199` or `g.crypto.bitcoin.1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2`.

When initiating an Interledger payment, the sender attaches an ILP packet to the local transfer to the connector. The packet is a binary message that includes the destination account, destination amount, and additional data for the receiver. The packet is relayed by connectors and attached to each transfer that comprises the payment. In some cases, ledger protocols may define alternative ways to communicate the packet.


The [Interledger Quoting Protocol (ILQP)](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md) defines how senders request quotes from connectors to determine the source or destination amount for an Interledger payment. Quoting is optional and senders MAY cache quotes and send repeated payments through the same connector.

### Transport Layer

Transport layer protocols are end-to-end protocols used by the senders and receivers of Interledger payments to determine the payment condition and other details. The guarantees afforded to the sender vary depending on the type of transport protocol used.

There are currently two transport layer protocols:

* [Pre-Shared Key (PSK)](../0016-pre-shared-key/0016-pre-shared-key.md)

    In Pre-Shared Key (PSK) protocol, the sender and receiver use a shared secret to generate the payment condition, authenticate the ILP packet, and encrypt application data. Using PSK, the sender is guaranteed that fulfillment of their transfer indicates the receiver got the payment, provided that no one aside from the sender and receiver have the secret and the sender did not submit the fulfillment.

    **PSK is recommended for most use cases.**

* [Interledger Payment Request (IPR)](../0011-interledger-payment-request/0011-interledger-payment-request.md)

    In the Interledger Payment Request (IPR) protocol, the receiver generates the payment details and condition. The receiver does not share the secret used to generate the condition and fulfillment with the sender or anyone else, but the sender must ask the recipient to generate and share a condition before sending each payment. IPR is primarily useful for building non-repudiable application layer protocols, in which the sender's posession of the fulfillment proves to third parties that the sender has paid the receiver for a specific obligation.

### Application Layer

The application layer is the top layer of the Interledger protocol suite. Protocols on this layer are responsible for:

1. Destination account discovery
2. Destination amount negotiation
3. Transport protocol selection and communication of associated details, such as the shared secret or condition
4. Additional details to be communicated in ILP packet data

An example of an application layer protocol is the [Simple Payment Setup Protocol (SPSP)](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).
SPSP uses Webfinger ([RFC 7033](https://tools.ietf.org/html/rfc7033)) and an HTTPS-based protocol for communicating account, amount, and Pre-Shared Key details from the receiver to the sender.

