---
title: The Connector to Connector protocol
draft: 3
---
# Connector to Connector protocol

## Discovery

Connectors discover their peers through out-of-band communication, or by looking at https://connector.land and contacting the administrator of another connector.

Once peered, two connectors have a ledger between them; this is often a ledger with just two accounts.

There are two ways for connectors to peer with each other: symmetric, and asymmetric. In symmetric peering, the ledger between the two connectors is administered
collaboratively by the two connectors, optionally relying on a trusted third party (validator). In asymmetric peering, the ledger is administered by one of the two
peers, and the other peer only keeps a non-authoritative shadow ledger.

Regardless of whether the connectors peer symmetrically or asymmetrically, the initiating connector somehow needs to exchange information with the other connector.
WebFinger can help with that.

Whether discovery is done with or without use of WebFinger, each peer ends up knowing:

* the protocol to use to send information like route broadcasts to the other connector
* the protocol to use to add updates to the peering ledger
* the currency code for the peering ledger
* the currency scale for the peering ledger

### WebFinger-based discovery
In WebFinger-based discovery, both peers still need some out-of-band communication channel, over which one
prospective peer tells the other:
* their intent, "Let's peer using WebFinger!"
* their own hostname
* the currency code they propose for the peer ledger
* the ledger scale they propose for the peer ledger

And the other peer response with:
* their agreement, "OK, let's peer using WebFinger for discover, and using that currency code and scale for the peer ledger!"
* their own hostname

Now, both peers look up each other's host resource, for instance:

* the server wallet1.com looks up https://wallet2.com/.well-known/webfinger?resource=https://wallet2.com
* the server wallet2.com looks up https://wallet1.com/.well-known/webfinger?resource=https://wallet1.com

This way, each peer has the other peer's public key. They now use ECDH to create a shared secret, from which a ledger prefix and an auth token are derived,
as implemented in [ilp-kit](https://github.com/interledgerjs/ilp-kit).

### Discovery without WebFinger
When the two connectors do their discovery without WebFinger, the first peer tells the other:
* their intent, "Let's peer without WebFinger!"
* a BTP URI for the other connector to use
* a BTP version to use (currently either 'BTP/alpha' or 'BTP/1.0')
* the currency code they propose for the peer ledger
* the ledger scale they propose for the peer ledger

And the other peer responds by connecting to the WebSocket indicated by the BTP URI and the protocol version. A BTP URI has one of the following formats:
* `btp+<protocol>://<auth_username>:<auth_token>@<url>`
* `btp+<protocol>://<auth_username>@<url>` // `auth_token === ''` is implied
* `btp+<protocol>://<url>` // `auth_username === ''` and `auth_token === ''` are implied

The `<protocol>` is either 'ws' or 'wss'. The `<url>` needs to contain a hostname, and may contain a port identifier and path part.

Examples:
* 'btp+ws://localhost:8000'
* 'btp+wss://someUsername:someToken@amundsen.michielbdejong.com/api/17q3'

Both connector-to-connector messages and ledger updates will then be transported over the BTP WebSocket.

Note that one peer will play the role of WebSocket server, and the other peer will play the role of WebSocket client. Often, but not necessarily, the peer
playing the server role will also administer the peer ledger, and the peer playing the client role will only keep a shadow ledger.

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
