---
title: Interledger server roles
draft: 1
---
# Interledger server roles

This document describes the different roles a server can play on the Interledger main net or testnet: connector, shop, and payee.

## The Connector Role

An Interledger Connector should expose one or more end-points for clients to connect with. The behavior of each end-point should
follow either [BTP/2.0](https://github.com/interledger/rfcs/blob/35e6dd7e065f3c3232304d012429d1b7e3eb0d39/0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md), [http-oer](https://github.com/interledger/rfcs/pull/349#issuecomment-350914252), or [http-head](https://github.com/interledger/rfcs/blob/de237e8b9250d83d5e9d9dec58e7aca88c887b57/0000-ilp-over-http.md).

On top of this, the server should respond to ilp/forwarded, ilp/il-dcp, ilp/il-balance, and route-broadcast requests (see below). If BTP is used, the server should also respond to [auth](https://github.com/interledger/rfcs/pull/372), and may also initiate ilp/forwarded, paychan, and route-broadcast requests, but not ilp/il-dcp, ilp/il-balance, or info requests. Depending on which settlement ledger is used, pther protocols should be implemented accordingly. For instance, https://github.com/interledgerjs/ilp-plugin-xrp-asym-server/issues/10 describes a number of additional protocols to be used for sending XRP payment channel claims.

### ILP
ILP packets are used for various purposes. The request has the form of an ILP Prepare, and the response has the form of an ILP Fulfill (if successful) or an ILP Reject (if unsuccessful).

#### il-dcp
If the destination address is `peer.config` then the server should respond as described in https://github.com/interledgerjs/ilp-protocol-ildcp/issues/1.

#### il-balance
If the destination address is `peer.balance` then the server should respond with the balance in the fulfillment data.

#### route-broadcast
ProtocolName `'ilp'` is overloaded for route broadcasts, as described in https://github.com/interledger/rfcs/issues/27
The syntax of such a method is defined by https://github.com/interledgerjs/ilp-connector/blob/v17.0.2/schemas/RoutingUpdate.json and https://github.com/interledgerjs/five-bells-shared/blob/v22.0.1/schemas/Routes.json.
The format is JSON, like:
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

#### forwarded
If the packet doesn't start with `0x7B` ('{'), and the destination address is neither `peer.config` nor `peer.balance`, then the connector should try to obtain the fulfillment by forwarding the payment to the shop or payee indicated by the address. It should have no more than a reasonable value for transaction fee charged, the time taken to pass on prepares and pass back fulfills, and the failure rate.

### Other BTP protocolNames
All other protocols are considered to be ledger-specific, see https://github.com/interledgerjs/ilp-plugin-xrp-asym-server/issues/10 in the case of XRP payment channels.

## The Shop Role

An Interledger Shop should expose one or more end-points where clients can pay for services using [HTTP-ILP, draft 3](https://interledger.org/rfcs/0014-http-ilp/draft-3.html) with [PSK2, draft 1](https://interledger.org/rfcs/0025-pre-shared-key-2/draft-1.html).

## The Payee Role

An Interleder Payee should expose one or more end-points where clients can pay someone using a [payment pointer](https://github.com/interledger/rfcs/blob/e949d28c19936e379e8fb5e6579b070ac66c018a/0000-payment-pointers/0000-payment-pointers.md) for `application/spsp+json` setup with [SPSP for PSK2](https://github.com/interledger/rfcs/blob/5641d91e806a8c3e27d97b91c76cacd13a87444b/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) and [PSK2, draft 1](https://interledger.org/rfcs/0025-pre-shared-key-2/draft-1.html).
