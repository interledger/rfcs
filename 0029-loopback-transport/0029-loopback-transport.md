---
title: The Loopback Transport Protocol (LT)
draft: 1
---
# Loopback Transport Protocol (LT)

The Loopback Transport protocol is a technique for transporting value over the Interledger. It relies on the establishment of a temporary, direct, ILPv4 link between sender and receiver (the loopback link). The flow is as follows.

## Flow

The following flow describes how the sender's loopback transfer module ("LT module") interacts with the application layer protocol, the receiver, and the ILPv4 network.

1. The loopback connection is established out of band. For instance, the application layer protocol may allow the receiver to specify a [BTP/2.0](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md) URL for the sender to connect to.
1. The sender's LT module is initialized with this open connection.
1. The sender's LT module discovers the loopback address using [IL-DCP](https://github.com/interledgerjs/ilp-protocol-ildcp).
1. The sender's application layer protocol tells the LT module to send a payment for a given source amount, and expiry time.
1. The sender's LT module chooses a fulfillment at random.
1. The sender's LT module creates the condition of their payment by computing the SHA-256 hash of the fulfillment.
1. The sender's LT module sets the destination address to the loopback address for this lookback link.
1. Using this condition, address, and amount, the sender's LT module prepares an ILPv4 payment to a connector of her choice.
1. The payment will find its way from this connector, via any number of additional connectors, to the receiver.
1. The receiver checks that the destination address matches the loopback address he announced to the sender over IL-DCP earlier, and forwards the ILPv4 `prepare` message to the sender, over the loopback link.
1. The sender's application layer protocol gets to decide whether the destination amount that looped back is sufficient and whether this particular loopback payment should be accepted or rejected.
1. The sender's LT module accepts or rejects the ILPv4 payment that looped back over the loopback link.
1. If for whatever reason the payment does not arrive in time, the LT module responds to the application layer protocol with an error message instead

## Sender implementation requirements

In order to *send* Interledger payments over the loopback protocol, the sender needs to implement:

* Their part of an ILPv4 connection with the receiver
* Their part of an ILPv4 connection with some connector
* An IL-DCP client, for discovering the loopback address
* A pseudo random generator for generating fulfillments
* The SHA256 hash algorithm, so that they can calculate which conditions to send

## Receiver implementation requirements

In order to receive Interledger payments over the loopback protocol, the receiver needs to implement:

* Their part of an ILPv4 connection with the sender
* Their part of an ILPv4 connection with some connector
* An IL-DCP server, where the sender can discover the loopback address
* Forwarding behavior, so that incoming packets destined for the loopback address are relayed to the sender
* The SHA256 hash algorithm, so that they verify the fulfillments that the sender produces

## How to use

When designing an application layer protocol, it's advisable to support both LT and PSK. Even though LT is far simpler than PSK, the extra loopback hop means that LT payments inherently have a higher latency than PSK payments, where the receiver can immediately fulfill incoming prepared payments. In situations where the sender can easily formulate instructions for the receiver about when to accept a payment and when not, and the sender trusts the receiver to execute these instructions in good faith, the speed up achieved with PSK means money needs to be tied up for less time, and this may translate to lower transaction fees, depending on connector pricing policies. So the application layer protocol needs to provide a choice between LT and PSK.

If LT is chosen, the loopback link needs to be established; this will usually require some data exchange (e.g., one of the two parties sends connection details to the other party).

The flow described above assumes one party only acts as the sender, and the other party only acts as the receiver, but once the loopback link is established, it can easily be used in both directions (in that case, each participant would send an IL-DCP request to the other participant, to ask for a loopback address).
