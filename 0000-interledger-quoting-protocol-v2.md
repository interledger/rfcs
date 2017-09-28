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

### Scope

ILQPv2 is intended for senders to determine the rate between the source and destination amounts for a payment.

It is primarily designed for individual payments. While it may be used for streams of payments, other protocols that actively take into account exchange rates changing over time may be better suited for such use cases.

### Operation

Senders may use a dedicated quoting module or ILQPv2 may be included in a Transport Layer protocol. A sender's ILQPv2 module is responsible for initiating specially crafted test payments to receivers. The receiver's ILQPv2 module is responsible for handling the incoming test payment and rejecting it with a specific error message.

## Overview

### Relation to Other Protocols

ILQPv2 uses payments sent with the Interledger Protocol. In order for this protocol to work, Interledger connectors MUST NOT reject payments where the amount in the ILP Packet exceeds what the connector thinks should be delivered to the receiver based on the accompanying transfer amount. Connectors SHOULD forward the payment and apply their normal exchange rate. Connectors MUST also relay error messages back to the sender.

ILQPv2 is intended to be used alongside Transport Layer protocols. It uses a transfer condition with a special prefix (`ffffffffffffff` in hexadecimal or `__________` in base64url encoding). Other end-to-end protocols SHOULD ignore to avoid interfering with ILQPv2 and other protocols that use well-known conditions.

## Model of Operation

### Fixed Source Amount

This details the steps for a sender to get a quote for a fixed source amount ("if I send this much, how much will the receiver get?"):

1. The sender constructs an ILP packet with the receiver's ILP Address, an amount equal to the maximum value for unsigned 64-bit integers (18446744073709551615), and no data.
2. The sender uses their ILP module to send the packet on a transfer with the amount set to the fixed source amount of their quote request.
3. Connectors forward the payment to the receiver. (Note that connectors that recognize the special condition MAY "forward" the payment without actually reserving funds, since they know the payment will not be executed.)
4. When the receiver is notified of the incoming transfer, they reject the transfer with an error message including the amount that arrived in the transfer and the amount of time they have before the transfer expires.
5. Connectors relay the error message back to the sender.
6. When the sender is notified that their test transfer was rejected, they inspect the error message to determine how much arrived at the receiver's ledger and how much time the receiver had to respond before the transfer would time out. The sender can then adjust the values before sending the actual payment.

### Fixed Destination Amount

The steps are the same as for Fixed Source Amount quotes, except that the transfer amount is set to an arbitrary probe value. When the sender gets the error response from the receiver, they compute the exchange rate based on the amount they sent and the amount that arrived. The sender then divides the fixed destination amount from the quote request by that exchange rate.

## Specification

### Condition

ILQPv2 test payments use the condition:

`fffffffffffffff8a5aa9fefdbed3fffffffffffffffffffffffffffffffffff`, encoded as hexadecimal.

Or `__________ilqp_v2-0________________________`, encoded in Base64-URL.

### Error Message Format

**TODO: Define a binary format**

Fields include:
- Error code: either `F08` (which is currently unused) or `F99: Application Error`
- Error name: `ILQPv2`
- Amount that arrived in the final transfer to the receiver
- Milliseconds between the final transfer expiry and when the receiver processed the notification

## Open Questions

1. Should this be a standalone protocol or should it be built into Transport Layer protocols like PSK? One advantage of building it into something like PSK is that in that case you could use the shared secret to authenticate and encrypt the quote message.
2. Will senders want to hide the fact that they are requesting a quote from connectors (for example by using data in the ILP Packet as opposed to a well-known condition to indicate that the payment meant as a quote request)? Connectors may have good reasons (such as DoS prevention) for wanting to avoid having lots of failed payments going through them. On the other hand, using a known condition could allow connectors that recognize this protocol to avoid placing funds on hold.
3. Should we try to figure out quoting for streaming payments now or is this fine for the moment?
4. How should the sender determine the expiry duration for the transfer they send? How likely are we to run into very slow ledgers? Should they have logic for increasing the timeout if necessary? They might not want to put the transfer on hold for too long if their ledger actually requires them to put their funds on hold (as opposed to recognizing that this is meant just as a quote request and won't be fulfilled).
