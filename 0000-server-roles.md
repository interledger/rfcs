---
title: Interledger server roles
draft: 1
---
# Interledger server roles

This document describes the different roles a server can play on the Interledger main net or testnet: sender, connector, or receiver.

## Bilateral links

All network participants should connect to one or more other network participants using one of four bilateral transfer protocols:
BTP/2.0-I, HTTP-OER-ASYNC, or HTTP-OER-SYNC. Note that for the two BTP/2.0 variations, one neighbor plays the server role; the other plays the client role.
For the two HTTP-OER variations, both neighbors implement an equal role.

Depending on which settlement ledger is used, side protocols (i.e., protocols with a protocolName other than `'ilp'`) should be implemented accordingly. For instance, https://github.com/interledgerjs/ilp-plugin-xrp-asym-server/issues/10 describes a number of additional protocols to be used for sending XRP payment channel claims.

All side protocols are considered to be ledger-specific, for instance see https://github.com/interledgerjs/ilp-plugin-xrp-asym-server/issues/10 in the case of XRP payment channels.

### BTP/2.0
BTP/2.0 is defined in [BTP (draft 7)](https://interledger.org/rfcs/0023-bilateral-transfer-protocol/draft-7.html).

### BTP/2.0-I
BTP/2.0-I is defined as BTP/2.0 with idempotency: each request should be repeated regularly until a response is received, and each time a repeated request is received, the same response should be given. This means each peer needs to remember the responses it send until the sender has stopped repeating that request, and has moved on to newer requests.

### HTTP-OER-ASYNC
HTTP-OER-ASYNC is defined as follows:
* each peer can make https POST requests to a webserver controlled by the other peer, using a bearer token in an Authorization header
* the URL path starts with a `/`, followed by the protocolName (`'ilp'` for Interledger packets, other protocolNames like `'paychan'` can be used for bilateral settlement)
* for protocolName `'ilp'`:
  * the path continues with a second `/`, and a unique request identifier string, so the URL looks like `https://example.com/ilp/3442196b-5fc7-4d60-a17e-a9416a77745b`.
  * the request body is an Interledger packet.
  * the response status code is 200 if the packet was received correctly
  * requests will be repeated idempotently until a 200 response is received
  * Fulfill and Reject requests use the same request identifier string as the Prepare request they correspond to

### HTTP-OER-SYNC
HTTP-OER-SYNC is like HTTP-OER-ASYNC, except that the Fulfill or Reject packet is immediately included in the response body of the Prepare request.
This means that there is no way to know whether Fulfill or Reject packets were delivered successfully, except for the assumption that if they were
not delivered successfully, then the other party would repeat the request.

## Connector requirements
On top of these bilateral relations, apart from the side protocols, the `'ilp'` protocol carries ILP packets for various purposes.
The request has the form of an ILP Prepare, and the response has the form of an ILP Fulfill (if successful) or an ILP Reject (if unsuccessful).
Encoded ILP-packets, the request types a connector should respond to are: ilp/forwarded, ilp/il-dcp, ilp/il-balance, and route-broadcast.

#### forwarded
If the destination address does not start with `peer.`, then the connector should try to obtain the fulfillment by forwarding the payment to the destination address. It may charge a reasonable transaction fee, require a reasonable amount of time to pass on prepares and pass back fulfills, and have a reasonable failure rate.

#### il-dcp
If the destination address is `peer.config` then the server should respond as described in https://github.com/interledgerjs/ilp-protocol-ildcp/issues/1.

#### il-balance
If the destination address is `peer.balance` then the server should respond with the balance as a signed `Int64` in the fulfillment data (positive values in the requester's favor).

#### route-broadcast
Route broadcasts should be implemented like in [ilp-connector v21.3.0](https://github.com/interledgerjs/ilp-connector/releases/tag/v21.3.0).

#### ping
The ping protocol should be implemented [like in ilp-connector v21.3.0](https://github.com/interledgerjs/ilp-connector/blob/v21.3.0/src/controllers/echo.ts).

## The Receiver Role

A receiver should run an [SPSP](https://github.com/interledger/rfcs/blob/5641d91e806a8c3e27d97b91c76cacd13a87444b/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) end-point to give out shared secrets and accept [PSK2 (draft 1)](https://interledger.org/rfcs/0025-pre-shared-key-2/draft-1.html) payments at its ILP address. Using the [payment pointer](https://github.com/interledger/rfcs/blob/e949d28c19936e379e8fb5e6579b070ac66c018a/0000-payment-pointers/0000-payment-pointers.md) for that SPSP endpoint, it may expose services that support payment pointer discovery. There are three options for doing this: paid APIs can support [HTTP-ILP, draft 3](https://interledger.org/rfcs/0014-http-ilp/draft-3.html), monetized web pages can support [web-monetization](), and web shops can support [web-payments]().

## The Sender Role

A sender may initiate Interledger payments by sending a Prepare packet to a neighbor. There are basically two ways to do this: circular payments, and end-to-end payments. A circular payment goes from the sender, via (generally) two or more connectors, back to the sender. This means the destination of the payment is under the sender's own control, and the Prepare packet loops back to the sender through one of the their other neighbors. The sender can therefore just create fulfillment randomly and keep it secret. They can then use that fulfillment's SHA256 hash as the payment's condition, and once the Prepare packet loops around, complete the circular payment by sending back a Fulfill packet, using the fulfillment they previously kept secret.

End-to-end payments go from a sender to a receiver. Using the receiver's payment pointer (discovered through one of the three methods mentioned about), the sender retrieves an SPSP record from the receiver, and uses PSK2 (draft 1) to determine the condition and data for which the receiver will be able to accept their payment.
