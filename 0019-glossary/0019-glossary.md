---
title: Glossary
draft: 3
---
# Glossary

## Account
An administrative item that acts as a bucket of assets on a ledger.

## Application Layer
The set of protocols built upon the [Transport Layer](#transport-layer) that communicate payment details between senders and receivers. Application Layer protocols specify all of the data and methods needed to set up a payment for a specific category of use cases or applications. For example, the Simple Payment Setup Protocol uses WebFinger and HTTPS for account detail lookup.

## Arbitrage
The practice of doing [cyclic transactions](#cyclic-transaction) which start and end on the same [ledger](ledger),
or groups of simultaneous transactions which add up to one cyclic transaction.
Taking advantage of quirks and fluctuations in exchange rates,
the goal is to achieve a [destination amount](#destination-amount) which is higher than the [source amount](#source-amount).

## Asset
Something you can own. Can be a physical and unique item, a quantity of a physical substance, a specific physical collection of coins and bank notes,
a non-physical quantity of currency, a non-physical claim to a resource, a reputation for keeping one's word, someone else's intention to obey the
terms of a contract, etc. Some types of assets can be more easily traded on a ledger than others. Also, for some asset pairs it is easier to determine
a fair exchange rate than for others.

## Balance
The amount of a ledger's assets held by a given account. This concept is not as clearly defined as it may seem at first glance.
When part of an account's balance is not readily usable, it is up to the ledger implementation to decide whether an account's
"balance" includes only the readily usable balance, or all of it, or some number inbetween.

## Centralized Ledger
A ledger which is operated by a single entity.

## Chunked Payment
A large payment which is split into smaller chunks that are then sent sequentially. Chunked payments reduce the total amount of money in-flight at a given time, which can reduce certain risks and costs.

## Conditional Transfer
Each local transfer is first *prepared* and then either *executed* or *rejected*. When a transfer is prepared, the ledger puts the funds of the source account on hold with a *cryptographic condition* and *timeout*. If the condition is fulfilled before the timeout, the transfer is executed and the funds are transferred. If the timeout is reached, the transfer expires and the ledger returns the funds to the source account automatically.
Inspired by the [Lightning Network](http://lightning.network), Interledger uses the digest of the [SHA-256](https://en.wikipedia.org/wiki/SHA-2) hash function as the condition for transfers. The fulfillment is a valid 32-byte preimage for the hash specified when the transfer was prepared. Ledgers are responsible for validating fulfillments. [Transport Layer](#transport-layer) protocols are used by the sender and receiver to generate the condition for a particular payment.

## Connector
A party who chains one transfer to the next in an interledger payment.
A connector receives a local transfer on one ledger in exchange for making another local transfer on a different ledger. A single interledger payment may include multiple connectors and may traverse any number of ledgers.
Connectors take some risk, but this risk can be managed and is primarily based upon the connector's chosen ledgers and direct peers.

## Cyclic Transaction
A transaction where the destination account is the same account, on the same ledger, as the source account. This can be useful
when rebalancing liquidity (to enable future payments), or when rebalancing stored value (to spread risk, or to take advantage
of changing exchange rates).

## Destination Account
The account of the receiver, whose address is included in the
[interledger packet](#interledger-packet).
Note that anyone can claim to have a certain [Interledger address](#interledger-address); address ownership is not enforced.

## Destination Amount
The amount to be received by the receiver.

## Destination Ledger
The ledger on which the final receiver of an Interledger payment holds their account

## Distributed Ledger
A ledger that is operated by a group of entities and/or run on multiple servers. This term is used somewhat interchangeably with "Blockchain" or "Decentralized Ledger".

## Exchange Rate
The price of one ledger's asset in terms of another ledger's asset.
Connectors may generate revenue from the difference in value between incoming and outgoing transfers.
Senders may request quotes from multiple connectors to determine the best price before sending a payment.
The exchange rate between source and destination is determined by the product of exchange rates at each hop.

## Executed
A final state of a transfer indicating that the funds were transferred to the account of the immediate recipient. See also [rejected](#rejected).

## Execution Phase
The second phase of an ILP payment, in which the fulfillment is passed back from the receiver, via the connector(s), to the sender.

## Final State
The state an interledger payment ends up in. Has to be either
[rejected](#rejected) or [executed](#executed).

## Fulfillment
A 32-byte value used to trigger the execution of a transfer. In most Interledger payments, the fulfillment is known only to the receiver
(or in the case of the Pre-Shared Key protocol it is known to the sender and the receiver). For more details see
[conditional transfer](#conditional-transfer).

## Hold
Part of the sender's, connector's, and/or receiver's account balance is "on hold" when that balance
is reserved for a specific ILP payment and is temporarily unavailable for use in other payments.
The money is on hold while the ILP transfer is in the `prepared` state.
If the transfer is executed, the money is no longer on hold, and added to the balance of the receiver of the transfer.
If the transfer is rejected, the money is no longer on hold either, but is instead returned to the balance of the sender of the transfer.

## Hop
One of the transfers that make up a payment. Specifically, a 'multi-hop' payment is one involving more than one ledger, and thus at least one connector.
Likewise, 'best hop', as used in the ilp-connector source code when making routing decisions, is best interpreted as 'best next transfer'.

## IL-RFC
Interledger request for comments. A document describing a part of the protocol stack, or a topic related to it, such as this glossary. The official list of IL-RFCs is maintained in
[gh:interledger/rfcs](https://github.com/interledgers/rfcs).

## Incoming (Transfer, Ledger, Amount)
The transfer/ledger/amount, relative to the party who plays the 'receiver' role. See also [Outgoing](#outgoing-transfer-ledger-amount).

## Interledger (in "Let's use Interledger for that!")
The [Interledger protocol stack](#interledger-protocol-stack).

## interledger (in "An interledger network")
Of a network of two or more ledgers, indicating that it uses the Interledger protocol stack. See also [Interledger (The)](#interledger-the)
The adjective 'interledger' is also sometimes used to simply refer to transactions that cross multiple ledgers, even if ILP is not used (similar to
'international' meaning 'across multiple nations').

## Interledger (in "The Interledger")
The main public network of ledgers connected via the Interledger protocol stack. See [ConnectorLand](https://connector.land) for statistics about it.

## Interledger Addresses
Interledger addresses provide a ledger-agnostic way to address ledgers and accounts. Interledger addresses are dot-separated strings that contain prefixes to group ledgers. An example address might look like `g.us.acmebank.acmecorp.sales.199` or `g.crypto.bitcoin.1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2`.
When initiating an Interledger payment, the sender attaches an ILP packet to the local transfer to the connector. The packet is relayed by connectors and attached to each transfer that comprises the payment. In some cases, ledger protocols may define alternative ways to communicate the packet.
Note that anyone can claim to have a certain Interledger address, there is no registry of them.
Whether or not a payment ends up at the intended receiver is ultimately safe-guarded by the hashlock condition,
not by enforcement of address ownership.
See [IL-RFC 15](../0015-ilp-addresses/0015-ilp-addresses.md)

## Interledger Architecture
The [Interledger protocol stack](interledger-protocol-stack), and the design principles behind it.

## Interledger Layer
The lowest layer of the Interledger protocol stack (not counting the 'ledger layer' below it), consisting of
the [ILP](#interledger-protocol-ilp) Interledger protocol, and the [ILQP](#ilqp) quoting protocol,

## Interledger Module
The part of a software application that processes ILP payments.
Analoguous to the network card of an internet-connected computer.

## Interledger Packet
The binary data packet that is forwarded along all hops from sender to receiver, and which provides the receiver
with metadata which they may need before they are willing and able to fulfill the payment.
It also contains the destination account's address and destination amount, on which connectors will base their routing decisions -
both in choosing the onward path, and in deciding whether their incoming amount was big enough, in comparison to the destination
amount mentioned in the ILP packet, to even merit an attempt to route the payment at all. See also [routing table](#routing-table).

## Interledger Payment Request (IPR)
A Transport Layer protocol in which the receiver generates the payment details and condition. The receiver does not share the secret used to generate the condition and fulfillment with the sender or anyone else, but the sender must ask the recipient to generate and share a condition before sending each payment. IPR is primarily useful for building non-repudiable application layer protocols, in which the sender's posession of the fulfillment proves to third parties that the sender has paid the receiver for a specific obligation.
See [IL-RFC 11](../0011-interledger-payment-request/0011-interledger-payment-request.md).

## Interledger Protocol (ILP)
The core of the Interledger protocol suite, described in [IL-RFC 3](../0003-interledger-protocol/0003-interledger-protocol.md).
Colloquially the whole Interledger stack is sometimes referred to as "ILP". Technically, however, the Interledger Protocol is only one layer in the
[Interledger protocol stack](#interledger-protocol-stack).

## Interledger protocol stack
The stack consisting of the [Interledger layer](#interledger-layer),
a choice of [transport layer](#transport-layer) protocols, and the [application layer](#application-layer).

## Interledger Quoting Protocol (ILQP)
The protocol that defines how senders request quotes from connectors to determine the source or destination amount for an Interledger payment. Quoting is optional and senders MAY cache quotes and send repeated payments through the same connector.
See [IL-RFC 8](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md).

## Intermediate (transfer, ledger, amount)
Any transfer/ledger/amount that is neither directly adjacent to the sender, nor to the receiver.

## Ledger
Stateful systems that track the ownership of [assets](#asset). Ledgers contain buckets of assets known as [accounts](#account) and record [transfers](#transfer) between them.
Each account has a [balance](#balance), which is the amount of the ledger's assets the account holds. Account balances may be positive or negative, representing assets or liabilities.

## Liquidity
Maximum amount which can be moved back and forth over a route.

## Local Payment
A payment that contains just one [transfer](#transfer) and zero [hops](#hop), thus staying within the same ledger.

## Outgoing (Transfer, Ledger, Amount)
The transfer/ledger/amount, relative to the party who plays the sender role. See also [Incoming](#incoming-transfer-ledger-amount).

## Payment
The movement of assets from one party to another. May imply that this movement is across multiple ledgers, as opposed to a local transfer.
A payment consists of one or more [ledger transfers](#transfer). Roughly synonymous with
[transaction](#transaction), and preferable in source code where 'transaction' may be confused with database transactions.
The word payment has an emphasis on the context of the negotiation between the sender and receiver. For instance,
it may be paying a debt, or a purchase, it may be a pull payment or a push payment. All these aspects which put a transaction in a wider
context and link it to real-world interactions, contracts, and motivations between parties make a transaction into a payment. A
[cyclic transaction](#cyclic-transaction) is generally not considered a payment, because the sending party of such a transaction is also the receiving party.

## Payment channel
A method used by two parties on the same ledger to make multiple transfers such that the ledger enforces the final net positions without the ledger being informed of each individual transfer. One or both parties will generally escrow some of their assets on the ledger and transfers are made by exchanging "claims" that update the net balance. When one of the parties wishes to close the channel, they submit the final balance to the ledger. Different implementations have different rules about which party is allowed to close the channel, the consequences of doing so, and the mechanisms for settling disputes. For more details see [Bitcoin Payment Channels](https://en.bitcoin.it/wiki/Payment_channels). Note that payment channels are similar to [trustlines](#trustlines) except the ledger is used to escrow one or both parties' assets and provide clear resolution mechanisms for disputes over the final net positions.

## Peer balance
See [trustline](#trustline).

## Peering
Connectors "peer" with one another to exchange information used to determine the best route for a payment, and to route it (connect its chain of
transfers during the [preparation phase](#preparation-phase) and [execution phase](#execution-phase).
A peering relationship is usually implemented using either a [trustline](#trustline) or a [payment channel](#payment-channel)..

This is similar to [how internet service providers peer with each other](https://en.wikipedia.org/wiki/Peering).

## Preparation Phase
The first phase of an ILP payment, in which the ILP packet is passed from the sender, via the connector(s), to the receiver.
Also, money is put [on hold](#hold) during this phase.

## Prepared
The state of a transfer in which the source account's funds are put on hold by the ledger until either the expiry is reached or the condition is fulfilled. See [Conditional Transfer](#conditional-transfer).

## Pre-Shared Key (PSK)
The recommended transport layer for most use cases.
In Pre-Shared Key (PSK) protocol, the sender and receiver use a shared secret to generate the payment condition, authenticate the ILP packet, and encrypt application data. Using PSK, the sender is guaranteed that fulfillment of their transfer indicates the receiver got the payment, provided that no one aside from the sender and receiver have the secret and the sender did not submit the fulfillment. See [IL-RFC 16](../0016-pre-shared-key/0016-pre-shared-key.md).

## Proposed
[DEPRECATED] The 'proposed' state of a payment is no longer used in practice; nowadays, payments skip this state, and are immediately created in their 'prepared' state.
The official [Interledger whitepaper](https://interledger.org/interledger.pdf) still describes it, though.

## Receiver
The party who is the beneficiary (payee) of a transfer or a payment (transaction).
When Alice sends a payment through a connector to Bob,
it's ambiguous whether by "the receiver" you mean the receiver of the transfer
(i.e., the connector), or the receiver of the payment (i.e., Bob), so use this
term carefully.

## Rejected
One of the final states a transfer can end up in, that means the funds have been returned to the sender. See also [executed](#executed).

## Route
A set of [transfers](transfer), chained together by the [connectors](#connector) between them.
This can refer to both the "route" an actual payment has taken or the theoretical
way that a future payment could go. The former is sometimes also called the path.

## Routing Table
A lookup table, used by a connector to decide who their outgoing receiver should be (the next
hop, which may be another connector, or the destination receiver), and what the lowest outgoing
amount is which they can safely offer for the outgoing transfer (equal to the destination amount in case
the outgoing is the destination transfer).

## Sender
The party who is the initiator (payer) of a transfer or a payment (transaction).

## Simple Payment Setup Protocol (SPSP)
SPSP uses Webfinger ([RFC 7033](https://tools.ietf.org/html/rfc7033)) and an HTTPS-based protocol for communicating account, amount, and Pre-Shared Key details from the receiver to the sender.
See [IL-RFC 9](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).

## Source (transfer, ledger, amount)
The transfer/ledger/amount directly adjacent to the sender.

## Streaming Payment
An ongoing payment where small amounts of money are sent over time to pay for some ongoing service or rent. For instance, a user might pay for a streaming video with a streaming payment. Or a tenant may pay rent as a streaming payment.

The amount sent in each iteration and the interval between iterations are inversely proportional. When the interval is long, e.g. a month, this would usually be called a subscription or recurring payment. The term "streaming payment" is commonly reserved for cases where the interval is short, from one second up to about a day.

## Transaction
See [Payment](#payment). Use of the term 'transaction' is discouraged, due to possible confusion
with for instance database transactions in source code.

## Transfer
The movement of assets on one single ledger. Multiple transfers can be chained together into one [multi-hop](#hop) [payment](#payment).
Also sometimes called 'ledger transfer'.

## Transport Layer
The middle layer of the Interledger protocol stack, which determines the condition and encoding of the data in the
ILP Packet, and what details the sender and receiver need to discuss beforehand. It can be either
either [Pre-Shared Key](#psk) or [Interledger Payment Request](#ipr). It is called the transport layer because
it provides the end-to-end hashlock condition which ultimately connects the individual
ledger transfers together, into one Interledger payment. In that sense, the transport layer "transports" the payment
over one or more transfers.

## Trustline
A trustline between two participating parties (participants) is a trust relationship between two parties,
in which each keep track of their own balance.
