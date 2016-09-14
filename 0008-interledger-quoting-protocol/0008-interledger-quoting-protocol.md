# Interledger Quoting Protocol (ILQP)

The Interledger Quoting Protocol is a method of getting quote information from a Connector in preparation for arranging transfers across two ledgers. The quote returned by a Connector is non-binding, but provides a basis for choosing which connectors to use.

There are two consumers of the ILQP: sending clients, and other connectors.

The HTTP+JSON interface for the ILQP is a temporary measure. Eventually, it should be replaced completely by a binary version.

## Background and Terminology

The quoting protocol returns the price of a _hypothetical_ payment through the connector being queried. However, no part of the ILQP initiates or creates an actual payment. All the information in the ILQP is non-binding and advisory. ILQP only calculates and reports the expected cost of a payment.

Accounts in ILQP are identified by their ILP Addresses. For a full explanation of ILP Addresses, see [Proposal: ILP Address Mapping](https://github.com/interledger/rfcs/issues/31). ***TODO: NEED BETTER REFERENCE***.

ILP payments can as simple as two transfers in different ledgers joined by a single connector. In other cases, they may be longer chains with multiple connectors across three or more ledgers. The response of an ILQP request only defines one link in the chain.

**Ledgers:**

* The **source ledger** is where the sender and the connector both have accounts.
* The **destination ledger** is where the receiver and the connector both have accounts.

The sending and receiving ledger are different ledgers. Otherwise, there should be no reason to use ILQP.

**Parties:**

* The **sender** is the party being debited at the start of the overall chain.
* The **source** is the party being debited in a single link of the chain. In a simple payment, the source is also the receiver.
* The **receiver** is the party being credited at the end of the overall chain.
* The **destination** receives money from the connector in a single link. In a simple payment, the destination is also the receiver.
* The **receiver** is the party being credited in the receiving ledger.
* A **connector** facilitates the payment between the source and destination in a single link. In a multiple-hop payment, there are multiple connectors, each of which is the destination of one link and the source of the next.

## Get Quote (HTTP)

This is the only API method in the HTTP+JSON version of the ILQP.

### Request Format

```
GET /
```

The request uses the following query parameters:

| Field                         | Type        | Description                    |
|:------------------------------|:------------|:-------------------------------|
| `source_address`              | ILP Address | Address of the source's account in the source ledger. |
| `destination_address`         | ILP Address | Address of the destination's account in the destination ledger. |
| `source_amount`               | Number      | Fixed amount to debit from the source's account. (Required unless `destination_amount` specified.) |
| `destination_amount`          | Number      | (Optional) Fixed amount to credit to the destination's account. (Required unless `source_amount` specified.) |
| `destination_expiry_duration` | Number      | (Optional) Number of milliseconds before the transfer in the destination ledger expires. |
| `source_expiry_duration`      | Number      | (Optional) Number of milliseconds before the transfer in the source ledger expires. |
| `slippage`                    | Number      | (Optional) Custom slippage ***amount? percentage?*** to assume for the exchange between ledgers. Lower slippage means the payment is cheaper but more likely to fail due to market movement. |

The request must specify either `source_amount` or `destination_amount` but not both.

Example request:

```
GET https://connector.example/?source_amount=100.25&source_address=eur-ledger.alice&destination_address=usd-ledger.bob&source_expiry_duration=6000&destination_expiry_duration=5
```

### Response Format

***TODO***

Example response:

```
HTTP/1.1 200 OK
{
  "source_connector_account": "mark",
  "source_ledger": "eur-ledger",
  "source_amount": "100.25",
  "source_expiry_duration": "6000",
  "destination_ledger": "usd-ledger",
  "destination_amount": "105.71",
  "destination_expiry_duration": "5000"
}
```

## Appendix A: ASN.1 Module

**TODO**: What's the best way to link this?

[InterledgerQuotingProtocol.asn](../asn1/InterledgerQuotingProtocol.asn)
