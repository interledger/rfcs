---
title: The Interledger Quoting Protocol (ILQP)
draft: 3
---
# Interledger Quoting Protocol (ILQP)

The Interledger Quoting Protocol is a method of getting quote information from a Connector in preparation for arranging transfers across two ledgers. The quote returned by a Connector is non-binding, but provides a basis for choosing which connectors to use.

There are two consumers of the ILQP: sending clients, and other connectors.

## Background and Terminology

The quoting protocol returns the price of a _hypothetical_ payment through the connector being queried. However, no part of the ILQP initiates or creates an actual payment. All the information in the ILQP is non-binding and advisory. ILQP only calculates and reports the expected cost of a payment.

Accounts ILQP are identified by their ILP Addresses. For a full explanation of ILP Addresses, see [ILP Addresses](../0015-ilp-addresses/0015-ilp-addresses.md).

ILP payments can be as simple as two transfers in different ledgers joined by a single connector. In other cases, they may be longer chains with multiple connectors across three or more ledgers. The response of an ILQP request combines the exchange rates of all links in the chain into one quote.

**Ledgers:**

* The **source ledger** is where the sender and the connector both have accounts.
* The **destination ledger** is where the receiver and the last connector both have accounts.

The source and destination ledger are different ledgers. Otherwise, there should be no reason to use ILQP.

**Parties:**

* The **sender** is the party who would be debited on the source ledger by the hypothetical payment.
* The **receiver** is the party being credited on the destination ledger by the hypothetical payment.
* A **connector** forms the active link between an incoming transfer on one ledger and an outgoing transfer on the next.

In a multiple-hop payment, there are multiple connectors, each of which creates an outgoing transfer in response to an incoming transfer. If the first connector in the chain has full (cached) pricing information, it will respond to the sender's quote request immmediately. If not, it will forward the quote request along the chain, and then relay the response it gets back.

> The following description of ILQP documents the current behaviour of nodes on the live Interledger, the majority of which are running [ILP Kit](https://github.com/interledgerjs/ilp-kit) software.

## Get Quote

Quotes are sent through a request/response mechanism exposed by the ledger plugins or ledger layer.

A quote request's `ilp` property must be a `QuoteLiquidityRequest`, `QuoteBySourceRequest`, or `QuoteByDestinationRequest`. The response's `ilp` property must be a `QuoteLiquidityResponse`, `QuoteBySourceResponse`, or `QuoteByDestinationResponse` respectively. If an error occurs during quoting, `ilp` will be a [`IlpError`](../0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-format) instead.

## ILQP Packets

See [interledgerjs/ilp-packet](https://github.com/interledgerjs/ilp-packet/) for an example implementation of a packet serializer/deserializer.

### QuoteLiquidityRequest

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `2` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| destinationAccount | Length-prefixed String | Address corresponding to the destination account |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |
| extensions | Length Determinant | Always `0` |

### QuoteLiquidityResponse

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `3` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| liquidity | LiquidityCurve | Curve describing the liquidity for the quoted route |
| appliesToPrefix | Length-prefixed String | Common prefix of all addresses for which this liquidity curve applies. |
| sourceHoldDuration | UInt32 | How long the sender should put the money on hold (in milliseconds) |
| expiresAt | Timestamp | Maximum time where the connector expects to be able to honor this liquidity curve. This MUST be expressed in the UTC + 0 (Z) timezone. |
| extensions | Length Determinant | Always `0` |

`LiquidityCurve` is encoded as a `SEQUENCE OF SEQUENCE { x UInt64, y UInt64 }`. This is a binary format, so for example the curve `[ [0, 0], [10, 265] ]` is equivalent to the base64-encoded string `"AAAAAAAAAAAAAAAAAAAAAAAAAAAKAAAAAAAAAAkBAAA="`.

See [interledgerjs/ilp-routing.LiquidityCurve](https://github.com/interledgerjs/ilp-routing/blob/master/src/lib/liquidity-curve.js) for an example implementation of a LiquidityCurve serializer/deserializer.

### QuoteBySourceRequest

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `4` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| destinationAccount | Length-prefixed String | Length-prefixed address corresponding to the destination account |
| sourceAmount | UInt64 | Amount the sender needs to send, denominated in the asset of the source ledger |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |
| extensions | Length Determinant | Always `0` |

### QuoteBySourceResponse

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `5` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| destinationAmount | UInt64 | Amount that will arrive at the receiver |
| sourceHoldDuration | UInt32 | How long the sender should put money on hold (in milliseconds) |
| extensions | Length Determinant | Always `0` |

### QuoteByDestinationRequest

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `6` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| destinationAccount | Length-prefixed String | Length-prefixed address corresponding to the destination account |
| destinationAmount | UInt64 | Amount that will arrive at the receiver |
| destinationHoldDuration | UInt32 | How much time the receiver needs to fulfill the payment (in milliseconds) |
| extensions | Length Determinant | Always `0` |

### QuoteByDestinationResponse

| Field | Type | Short Description |
|:--|:--|:--|
| type | Byte | Always `7` |
| length | Length Determinant | One or more bytes, indicating how many bytes follow in the rest of the packet |
| sourceAmount | UInt64 | Amount the sender needs to send, denominated in the asset of the source ledger |
| sourceHoldDuration | UInt32 | How long the sender should put money on hold (in milliseconds) |
| extensions | Length Determinant | Always `0` |

## Next Steps

After getting a quote using ILQP, the client can display the quote to the user and optionally proceed to _Preparing_ (also called _Setting Up_) the payment, for example using the [Simple Payment Setup Protocol](https://github.com/interledger/rfcs/tree/master/0009-simple-payment-setup-protocol). That process actually sets money aside and creates the crypto-conditions that will release the money to the desired parties.

## Appendix A: ASN.1 Module

The [InterledgerQuotingProtocol.asn](../asn1/InterledgerQuotingProtocol.asn) ASN.1 module describes the binary ILQP messages.
