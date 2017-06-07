# Interledger Quoting Protocol (ILQP)

The Interledger Quoting Protocol is a method of getting quote information from a Connector in preparation for arranging transfers across two ledgers. The quote returned by a Connector is non-binding, but provides a basis for choosing which connectors to use.

There are two consumers of the ILQP: sending clients, and other connectors.

## Background and Terminology

The quoting protocol returns the price of a _hypothetical_ payment through the connector being queried. However, no part of the ILQP initiates or creates an actual payment. All the information in the ILQP is non-binding and advisory. ILQP only calculates and reports the expected cost of a payment.

Accounts ILQP are identified by their ILP Addresses. For a full explanation of ILP Addresses, see [ILP Addresses](../0015-ilp-addresses/0015-ilp-addresses.md).

ILP payments can be as simple as two transfers in different ledgers joined by a single connector. In other cases, they may be longer chains with multiple connectors across three or more ledgers. The response of an ILQP request only defines one link in the chain.

**Ledgers:**

* The **source ledger** is where the sender and the connector both have accounts.
* The **destination ledger** is where the receiver and the connector both have accounts.

The sending and receiving ledger are different ledgers. Otherwise, there should be no reason to use ILQP.

**Parties:**

* The **sender** is the party being debited at the start of the overall chain.
* The **source** is the party being debited in a single link of the chain.
* The **receiver** is the party being credited at the end of the overall chain.
* The **destination** is the party being credited in a single link of the chain.
* A **connector** facilitates the payment between the source and destination in a single link. In a multiple-hop payment, there are multiple connectors, each of which is the destination of one link and the source of the next.

> The following description of ILQP documents the current behaviour of nodes on the live Interledger, the majority of which are running [ILP Kit](https://github.com/interledgerjs/ilp-kit) software.

## Get Quote

Quotes are sent through a request/response mechanism exposed by the ledger plugins or ledger layer.

A quote request's `ilp` property must be an `IlqpLiquidityRequest`, `IlqpBySourceRequest`, or `IlqpByDestinationRequest`. The response's `ilp` property must be an `IlqpLiquidityResponse`, `IlqpBySourceResponse`, or `IlqpByDestinationResponse` respectively. If an error occurs during quoting, `ilp` will be a [`IlpError`](../0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-format) instead.

## ILQP Packets

See [interledgerjs/ilp-packet](https://github.com/interledgerjs/ilp-packet/) for an example implementation of a packet serializer/deserializer.

### IlqpLiquidityRequest

| Field | Type | Short Description |
|:--|:--|:--|
| destinationAccount | Address | Address corresponding to the destination account |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |

### IlqpLiquidityResponse

| Field | Type | Short Description |
|:--|:--|:--|
| liquidity | LiquidityCurve | Curve describing the liquidity for the quoted route |
| appliesToPrefix | Address | Common prefix of all addresses for which this liquidity curve applies. |
| sourceHoldDuration | UInt32 | How long the sender should put the money on hold (in milliseconds) |
| expiresAt | Timestamp | Maximum time where the connector expects to be able to honor this liquidity curve |

`LiquidityCurve` is encoded as a `SEQUENCE OF SEQUENCE { x UInt64, y UInt64 }`. This is a binary format, so for example the curve `[ [0, 0], [10, 265] ]` is equivalent to the base64-encoded string `"AAAAAAAAAAAAAAAAAAAAAAAAAAAKAAAAAAAAAAkBAAA="`.

See [interledgerjs/ilp-routing.LiquidityCurve](https://github.com/interledgerjs/ilp-routing/blob/master/src/lib/liquidity-curve.js) for an example implementation of a LiquidityCurve serializer/deserializer.

### IlqpBySourceRequest

| Field | Type | Short Description |
|:--|:--|:--|
| destinationAccount | Address | Address corresponding to the destination account |
| sourceAmount | UInt64 | Amount the sender needs to send, denominated in the asset of the source ledger |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |

### IlqpBySourceResponse

| Field | Type | Short Description |
|:--|:--|:--|
| destinationAmount | UInt64 | Amount that will arrive at the receiver |
| sourceHoldDuration | UInt32 | How long the sender should put money on hold (in milliseconds) |

### IlqpByDestinationRequest

| Field | Type | Short Description |
|:--|:--|:--|
| destinationAccount | Address | Address corresponding to the destination account |
| destinationAmount | UInt64 | Amount that will arrive at the receiver |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |

### IlqpByDestinationResponse

| Field | Type | Short Description |
|:--|:--|:--|
| sourceAmount | UInt64 | Amount the sender needs to send, denominated in the asset of the source ledger |
| sourceHoldDuration | UInt32 | How long the sender should put money on hold (in milliseconds) |

## Next Steps

After getting a quote using ILQP, the client can display the quote to the user and optionally proceed to _Preparing_ (also called _Setting Up_) the payment, for example using the [Simple Payment Setup Protocol](https://github.com/interledger/rfcs/tree/master/0009-simple-payment-setup-protocol). That process actually sets money aside and creates the crypto-conditions that will release the money to the desired parties.

## Appendix A: ASN.1 Module

The [InterledgerQuotingProtocol.asn](../asn1/InterledgerQuotingProtocol.asn) ASN.1 module describes the binary ILQP messages.
