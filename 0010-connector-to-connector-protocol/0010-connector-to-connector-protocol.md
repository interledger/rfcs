---
title: The Connector to Connector protocol
draft: 2
---
# Connector to Connector protocol

## Discovery

Connectors discover their peers through out-of-band communication, or by looking at https://connector.land and contacting the administrator of another connector.

Once peered, two connectors have a ledger between them; this is often a ledger with just two accounts, often administered collaboratively by the two connectors.

## Route broadcasts

Connectors send each other `broadcast_routes` messages, using the message sending functionality of the ledger between them.

The syntax of such a method is defined by https://github.com/interledgerjs/ilp-connector/blob/v17.0.2/schemas/RoutingUpdate.json and
 https://github.com/interledgerjs/five-bells-shared/blob/v22.0.1/schemas/Routes.json.

When a route is included in a route update from Alice to Bob, Alice is stating she will, at least temporarily, be able to forward a payment to that destination, if the
source amount which Bob would send her is high enough, given the destination amount, and as described by the `points` piece-wise linear function.

Connectors also exchange quote requests,
in the same way users may request a quote from a connector, see [IL-RFC 8](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md).
This process is called remote quoting.

Note that the points series ("liquidity curves") in route broadcasts, as well as the
amounts in quote requests and quote responses, are expressed in integer values in the ledger's base unit of the ledger. This means you will need to divide/multiply
by `10 ** currency_scale` for the ledger in question, to convert integers (in ledger units) to floats (in terms of the ledger's announced `currency_code`), and back.

The curve from the route broadcast is used directly for determining a source amount / destination amount relation, and remote quoting is only used when
a connector knows about a route without knowing its curve information (this can happen if a connector somewhere in the network was explicitly configured with a hard-wired
(default) route in its ilp-connector config; that route then also gets forwarded without curve in route broadcasts across the network, and all connectors that want to use this
route will therefore need to use remote quoting).
All routes that were built up from local pairs will however get broadcast including their curves, based on connector fees, currency exchange rates, and liquidity limits (min and
max limits on the connector's balance on both ledgers) and this requires routes to be re-broadcast when their liquidity curve changes, but ilp-kit will aggregate over time, both
for its own liquidity changes, and route changes which it forwards, into one message per 30 seconds.

When combining various alternative (parallel) routes, for each section of the liquidity curve, ilp-kit will only consider routes which are as short as the shortest known route,
and from the set of shortest paths, choose the cheapest one. Note that the routing table of each ilp-kit is used for two things:

* determine whether a payment's source amount is sufficient or not, given its destination amount
* if so, choose the next hop (it's then up to that peer to choose the hop after that, until the destination node is reached)

## Please expand this document

This document is a stub, please help expand it! See https://github.com/interledger/rfcs.
