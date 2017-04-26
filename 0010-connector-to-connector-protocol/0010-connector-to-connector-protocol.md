# Connector to Connector protocol

## Discovery

Connectors discover their peers through out-of-band communication, or by looking at https://connector.land and contacting the administrator of another connector.

Once peered, two connectors have a ledger between them; this is often a ledger with just two accounts, often administered collaboratively by the two connectors.

## Route broadcasts

Connectors send each other `broadcast_routes` messages, using the message sending functionality of the ledger between them.

The syntax of such a method is defined by https://github.com/interledgerjs/ilp-connector/blob/v17.0.2/schemas/RoutingUpdate.json and
 https://github.com/interledgerjs/five-bells-shared/blob/v22.0.1/schemas/Routes.json.

When a route is included in a route update from Alice to Bob, Alice is stating she will probably be able to forward a payment to that destination, if the
source amount which Bob would send her is high enough, given the destination amount, and as described by the `points` piece-wise linear function, and if
liquidity permits.

This means that even if the points series in a broadcasted route gives values for higher amounts, routability is still conditional on Bob's balance being
sufficient when he tries to send a payment over the announced route, and Alice's balance on the next ledger being sufficient,
and the next connector's balance on the next ledger, etcetera.

Connectors also exchange quote requests, in the same way users may request a quote from a connector, see [IL-RFC 8](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md).

Note that, although Transfers and ledger plugin Balances are now all expressed in integer ledger units, the points series ("liquidity curves") in route broadcasts, as well as the
amounts in quote requests and quote responses, are still expressed in float values in the `currency_code` of the ledger. This means you will need to multiply/divide
by `10 ** currency_scale` for the ledger in question, to convert floats (in the currency) to integers (in ledger units), and back.

## Please expand this document

This document is a stub, please help expand it! See https://github.com/interledger/rfcs.
