---
title: Interledger server roles
draft: 1
---
# Interledger server roles

This document describes the different roles a server can play on the Interledger main net or testnet: connector, shop, and payee.

## The Connector Role

An Interledger Connector should expose one or more end-points for clients to connect with. The behavior of each end-point should
follow either [BTP/2.0](https://github.com/interledger/rfcs/pull/360), [http-oer](https://github.com/interledger/rfcs/pull/349#issuecomment-350914252), or [http-head](https://github.com/interledger/rfcs/blob/de237e8b9250d83d5e9d9dec58e7aca88c887b57/0000-ilp-over-http.md).

On top of this, the server should respond to ilp/forwarded, ilp/il-dcp, ilp/il-balance, info, paychan (various), and route-broadcast requests (see below). If BTP is used, the server should also respond to [auth](https://github.com/interledger/rfcs/pull/372), and may also initiate ilp/forwarded, paychan, and route-broadcast requests, but not ilp/il-dcp, ilp/il-balance, or info requests.

### ILP
ILP packets are used for various purposes. The request has the form of an ILP Prepare, and the response has the form of an ILP Fulfill (if succcessful) or an ILP Reject (if unsuccessful).

#### il-dcp
If the destination address is `peer.config` then the server should respond as described in https://github.com/interledgerjs/ilp-protocol-ildcp/issues/1.

#### il-balance
If the destination address is `peer.balance` then the server should respond with the balance in the fulfillment data.

#### forwarded
If the destination address is neither `peer.config` nor `peer.balance`, then the connector should try to obtain the fulfillment by forwarding the payment to the shop or payee indicated by the address.

### info
If the info request call type is `0`, the server should respond with JSON like https://github.com/interledgerjs/ilp-plugin-xrp-asym-server/blob/v1.0.3/index.js#L93-L96
Info request call type `1` is deprecated in favor of ILP/il-dcp.

### paychan
These are actually several ones, and depend on the underlying ledger used. If the underlying ledger is XRP, the server should respond to the following request types:
#### `channel`
[...]

#### `fund_channel`
[...]

#### `channel_signature`
[...]

#### `claim`
[...]

#### `last_claim`
[...]

#### `ripple_channel_id`
[...]

### route-broadcast
I have to look up what protocolName is used, but the format is JSON, like:
```js
{
  method: 'broadcast_routes'
  data: {
    hold_down_time: <integer>,
    unreachable_through_me: [
      <ILP address>,
    ],
    new_routes: [
      {
        destination_ledger: <ILP prefix>,
        min_message_window: <seconds>
      },
    ]
  }
}
```
 messages, using the message sending functionality of the ledger between them.

The syntax of such a method is defined by https://github.com/interledgerjs/ilp-connector/blob/v17.0.2/schemas/RoutingUpdate.json and https://github.com/interledgerjs/five-bells-shared/blob/v22.0.1/schemas/Routes.json.
## The Shop Role

An Interledger Shop should expose one or more end-points where clients can pay for services using http-ilp.

## The Payee Role

An Interleder Payee should expose one or more end-points where clients can pay someone using a payment pointer.
