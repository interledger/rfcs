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

### Current situation: gratuity quoting
Even though the first connector has a complete copy of all the liquidity curves, these curves might be out of date; they are used
to determine the best route, but not to determine which combination of source amount and destination amount the sender should use for a specific payment.
This situation allows each connector along the path to charge a "gratuity" in the quote, which was not included in the broadcasted curve, like the one that sometimes included
in the bill in a restaurant, on top of the price that was quoted in the menu.

Although this strategy works well in closed networks where each participant is vetted and can be trusted, it is known to be sub-optimal for use in an open network where connectors
may try to earn extra money by charging a higher fee than the cost price. Therefore, this "gratuity quoting" strategy used by the ilp-kit/ilp-connector reference implementation is
likely to change in the future, and one proposal is currently being developed.

### Next version: Liquidity Routing
In Liquidity Routing, the curve from the route broadcast is used directly for determining a source amount / destination amount relation, and remote quoting is only used when
a (default) route was configured without curve information. This requires routes to be re-broadcast when their liquidity curve changes, but ilp-kit will aggregate over time, both
for its own liquidity changes, and route changes which it forwards, into one message per 30 seconds.

When combining various alternative (parallel) routes, for each section of the liquidity curve, ilp-kit will only consider routes which are as short as the shortest known route,
and from the set of shortest paths, choose the cheapest one. Note that the routing table of each ilp-kit is used for two things:

* determine whether a payment's source amount is sufficient or not, given its destination amount
* if so, choose the next hop (it's then up to that peer to choose the hop after that, until the destination node is reached)

## Please expand this document

This document is a stub, please help expand it! See https://github.com/interledger/rfcs.
