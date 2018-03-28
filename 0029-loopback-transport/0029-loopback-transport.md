---
title: The Loopback Transport Protocol (LT)
draft: 1
---
# Loopback Transport Protocol (LT)

The Loopback Transport protocol is a technique for transporting value over the Interledger. It relies on the establishment of a temporary, direct, ILPv4 link between sender and receiver (the loopback link). The flow is as follows.

## One-shot Flow

1. The loopback connection is established out of band (see also [discovery](#discovery)). For instance, the application layer protocol may allow the receiver to specify a [BTP/2.0](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md) URL for the sender to connect to.
1. The sender discovers the loopback address using [IL-DCP](https://github.com/interledgerjs/ilp-protocol-ildcp).
1. The sender's application layer protocol tells the LT module to send a payment for a given source amount, minimum destination amount, and expiry time.
1. The sender chooses a fulfillment at random.
1. The sender creates the condition of their payment by computing the SHA-256 hash of the fulfillment.
1. The sender sets the destination address to the loopback address for this lookback link.
1. Using this condition, address, and amount, the sender prepares an ILPv4 payment to a connector of her choice.
1. The payment will find its way from this connector, via any number of additional connectors, to the receiver.
1. The receiver checks that the destination address matches the loopback address he announced to the sender earlier, and forwards the ILPv4 `prepare` message to the sender, over the loopback link.
1. The sender's LT module checks the destination amount and the time left before expiry are sufficient, and if so, uses the fulfillment to fulfill the payment.
1. If for whatever reason the payment does not arrive in time, or the minimum destination amount is not met, the LT module responds to the application layer protocol with an error message instead

## Chunked Flow

Wnen sending multiple ILPv4 payments, as chunks in a chunked payment, the parameters passed from application layer to the transport layer are different. The application layer specifies a desired cummulative destination amount, and a deadline. The transport layer module then creates chunks of varying size and expiry duration, and accepts only the chunks whose exchange rate is best. If the cummulative value of chunks accepted so far is behind schedule for reaching the desired total before the deadline, chunks that arrive with slightly worse exchange rates will be accepted too. If the cummulative value is increasing ahead of schedule, the threshold will be adjusted to accept only the chunks with the very best exchange rates.

## How to use

When designing an application layer protocol, it's advisable to support both LT and PSK. Even though LT is far simpler than PSK, the extra loopback hop means that LT payments inherently have a higher latency than PSK payments, where the receiver can immediately fulfill incoming prepared payments. In situations where the sender can easily formulate instructions for the receiver about when to accept a payment and when not, and the sender trusts the receiver to execute these instructions in good faith, the speed up achieved with PSK means money needs to be tied up for less time, and this may translate to lower transaction fees, depending on connector pricing policies. So the application layer protocol needs to provide a choice between LT and PSK.

If LT is chosen, the loopback link needs to be established; this will usually require some data exchange (e.g., one of the two parties sends connection details to the other party).

The flow described above assumes one party only acts as the sender, and the other party only acts as the receiver, but once the loopback link is established, it can easily be used in both directions (in that case, each participant would send an IL-DCP request to the other participant, to ask for a loopback address).

Once the loopback link is up, and each party who wants to act as a sender knows what their loopback address is, LT exposes two methods and one event to the application layer: one method for the one-shot flow, one for the chunked flow, one event that gets triggered whenever an incoming payment gets fulfilled, and one for when an outgoing payment gets fulfilled.

It is up to the application layer protocol to decide how much to send, and whether to use a one-shot or a chunked flow.

In future, hooks may be provided through which the application layer can also decide to reject incoming payments instead of looping them back to the appropriate sender.

## Discovery

A loopback server can be defined in the Loopback Server Definition (LSD) format, whose mime-type is `application/lsd+json`:

```js
{
  loopback: 'wss+btp://token@example.com/'
  protocol: 'BTP/2.0'
}
```
