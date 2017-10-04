---
title: Interledger Quoting Protocol v2 (ILQPv2)
draft: 1
---

# Interledger Quoting Protocol v2 (ILQPv2)

Replaces IL-RFC-8: Interledger Quoting Protocol, which should be considered deprecated if this proposal is accepted.

## Preface

ILQPv2 is an end-to-end protocol implemented by Interledger senders and receivers (**not** connectors, in contrast to ILQPv1). It allows a sender to determine the exchange rate between their ledger and the receiver's ledger by sending a specially crafted test payment to the receiver.

## Introduction

### Motivation

In general, the motivation for a quoting protocol is to allow senders to determine the exchange rate between their assets and the receiver's assets before making a payment.

The motivations for replacing ILQPv1 are as follows:

1. **Simplification of the Interledger Layer and Connector** - Previously, all Interledger connectors needed to implement both the Interledger Protocol and the Interledger Quoting Protocol in order to be fully compatible with the protocol. By making quoting an end-to-end concern, this simplifies connector implementations and what we think of as the Interledger Layer of the stack.
2. **Futility of Relying on Connector Quotes** - ILQP quotes were never intended to be binding, but rather to give senders a sense of the expected cost of a payment. Aside from the problems posed by malicious connectors, there were other reasons that quotes could not be relied upon. For example, exchange rates and connectors' liquidity positions are likely to change over time, rendering even honest quotes untrustworthy.
3. **Recognition of Quoting as an Application-Specific Concern** - Given the unreliability of quotes, different applications will need to handle fluctuating rates and liquidity differently. For example, the mechanism used to judge the cost of a stream of payments versus a single payment must actively take into account the changing rates. This suggests that different applications may need different types of quoting functionality or may not use quoting at all.
4. **Enabling Evolution of the Quoting Protocol** - Protocols on the Interledger Layer must be implemented by all participants and will thus be more difficult to update. Taking quoting out of the realm of connectors will enable different quoting protocols to evolve over time.

Note that ILQPv2 assumes all connector exchange rates are linear, rather than using Liquidity Curves like ILQPv1. See [Appendix A: Linear Exchange Rates](#appendix-a-linear-exchange-rates) for details.

### Scope

ILQPv2 is intended for senders to determine the rate between the source and destination amounts for a payment.

It is primarily designed for individual payments. While it may be used for streams of payments, other protocols that actively take into account exchange rates changing over time may be better suited for such use cases.

### Operation

Senders may use a dedicated quoting module or ILQPv2 may be included in a Transport Layer protocol. A sender's ILQPv2 module is responsible for initiating specially crafted test payments to receivers. The receiver's ILQPv2 module is responsible for handling the incoming test payment and rejecting it with a specific error message.

## Overview

### Relation to Other Protocols

ILQPv2 uses payments sent with the Interledger Protocol. In order for this protocol to work, Interledger connectors MUST ignore the amount in the ILP Packet, and neither attempt to deliver the exact amount in the packet or reject payments where the transfer amount is lower than the amount in the packet. Connectors MUST relay error messages back to the sender.

ILQPv2 is intended to be incorporated into Transport Layer protocols. Transport Protocols such as the Pre-Shared Key protocol should ensure that the normal logic for fulfilling or rejecting transfers does not interfere with ILQPv2.

## Model of Operation

### Fixed Source Amount

This details the steps for a sender to get a quote for a fixed source amount ("if I send this much, how much will the receiver get?"):

1. The sender constructs an ILP packet with the receiver's ILP Address, an amount of `0`, and data beginning with `ILQP/2.0\n`.
2. The sender uses their ILP module to send the packet on a transfer with the amount set to the fixed source amount of their quote request.
3. Connectors forward the payment to the receiver. (Note that connectors that recognize the special condition MAY "forward" the payment without actually reserving funds, since they know the payment will not be executed.)
4. When the receiver is notified of the incoming transfer, they reject the transfer with an error message including the amount that arrived in the transfer and the amount of time they have before the transfer expires.
5. Connectors relay the error message back to the sender.
6. When the sender is notified that their test transfer was rejected, they inspect the error message to determine how much arrived at the receiver's ledger and how much time the receiver had to respond before the transfer would time out. The sender can then adjust the values before sending the actual payment.

### Fixed Destination Amount

The steps are the same as for Fixed Source Amount quotes, except that the transfer amount is set to an arbitrary probe value. When the sender gets the error response from the receiver, they compute the exchange rate based on the amount they sent and the amount that arrived. The sender then divides the fixed destination amount from the quote request by that exchange rate.

Note that ILQPv2 assumes all connector exchange rates are linear. See [Appendix A: Linear Exchange Rates](#appendix-a-linear-exchange-rates) for details.

## Specification

### Test Payment Fields

#### ILP Packet Amount

The `amount` SHOULD be set to `0`.

#### ILP Packet Data

The `data` field MUST start with the UTF-8 string `ILQP/2.0\n`. The `data` field MAY contain other data, although ILQPv2.0 does not specify the use or encoding for this additional data.

#### Condition

ILQPv2 test payments SHOULD use the condition:

`0000000000000000000000000000000000000000000000000000000000000000`, encoded as hexadecimal.

Or `AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA`, encoded in Base64-URL.

#### Expiry

Test payments are RECOMMENDED to use a transfer expiry of 60 seconds.

If the first attempt at a quote request is rejected with an `R02: Insufficient Timeout` error, the sender MAY increase the expiry and retry.

### Error Message Format

The receiver MUST reject the test payment with an ILP Error of the form:

- Status Code: `S00`
- Status Name: `Ok`
- Data:

```asn.1
IlqpResponse ::= SEQUENCE {
  destinationAmount UInt64 -- Amount that arrived at the destination
}
```

## Alternatives Considered

### Encrypted Quotes

Senders MAY wish to hide the fact that certain transfers are intended as quote requests, for example if connectors attempt to block payments that are likely to fail. Instead of using a well-known condition and sending the string `ILQP/2.0\n` in the clear, senders could, for example, send payments that look from the outside like normal Pre-Shared Key (PSK) payments. The condition could be a random string, for which the fulfillment is not known and the fact that the payment is for quoting could be communicated inside the encrypted PSK data.

This option was not chosen because it is slightly more complicated, more tied to PSK, and may not effectively hide which payments are being used for quotes. For example, if implementations always send a quote as the first payment, connectors could identify these just by determining whether a given payment is the first in a series.

Furthermore, using a well-known condition makes it so that connectors MAY implement special logic to avoid placing funds on hold for payments that are guaranteed to be rolled back. This would reduce the burden of failed payments on connectors, which would reduce their incentive to block such payments in the first place.

## Appendix A: Linear Exchange Rates

In contrast to ILQPv1, ILQPv2 assumes that all connectors use linear exchange rates. This means that connectors SHOULD NOT charge different rates for payments of different sizes.

The motivations for this change are as follows:

1. **If paths have a relatively small Maximum Transfer Size (MTS), exchange rates should not need to vary** - Whether we like it or not, there will be a maximum size for an individual payment that the network will support. Between the Interledger Universal mode risk and liquidity issues, connectors will likely be incentivized to keep the MTS relatively small. If that's the case, there is less of a reason to vary the rate based on the size. Charging a different rate for a payment of $0.01 versus $10 makes less sense than charging a different rate for a payment of $100 million.
2. **Curves don't help for streaming payments** - If the MTS is smaller than the payments some people want to make, streaming payments will be required to chunk those payments up. In the case of streaming payments, the sender needs to understand the liquidity information over time, rather than just a static snapshot. Attempting to express liquidity over time would be too complicated to be worth it. But without that dynamic view, the snapshot curve does not help because it could change anyway. Therefore, in the case of streaming payments, senders will need to start sending, constantly monitor the rate, and adjust who they are sending through if the rate changes a lot.
3. **Assuming liquidity curves are just lines significantly simplifies routing** - Routing money is more complex than routing IP packets, which is already very complex. If connectors needed to route packets in different directions based on the payment size, connectors would need to maintain multiple routing tables for different sizes. This would make routing even more complex.
4. **We didn't use curves in practice** - When we were running the community network of ilp-kits, everyone was just using a % spread on top of a linear exchange rate pulled from fixer.io. It seems unlikely that connectors will need more complicated fee structures than that, and connectors may end up charging customers on monthly or other bases rather than per-payment.
5. **Simplification** - If there is a way to make the system work without liquidity curves, then they should be removed. "Perfection is achieved, not when there is nothing more to add, but when there is nothing left to take away."

