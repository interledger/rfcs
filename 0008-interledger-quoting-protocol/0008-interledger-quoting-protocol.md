# Interledger Quoting Protocol (ILQP)

The Interledger Quoting Protocol is a method of getting quote information from a Connector in preparation for arranging transfers across two ledgers. The quote returned by a Connector is non-binding, but provides a basis for choosing which connectors to use.

There are two consumers of the ILQP: sending clients, and other connectors.

The JSON interface for the ILQP is a temporary measure. Eventually, it should be replaced completely by a binary version.

## Background and Terminology

The quoting protocol returns the price of a _hypothetical_ payment through the connector being queried. However, no part of the ILQP initiates or creates an actual payment. All the information in the ILQP is non-binding and advisory. ILQP only calculates and reports the expected cost of a payment.

Accounts in ILQP are identified by their ILP Addresses. For a full explanation of ILP Addresses, see [Proposal: ILP Address Mapping](https://github.com/interledger/rfcs/issues/31) and [Fowarding/Delivery Distinction](https://github.com/interledger/rfcs/issues/77).

<!--{# ***TODO: Better reference for ILP addresses***. #}-->

ILP payments can as simple as two transfers in different ledgers joined by a single connector. In other cases, they may be longer chains with multiple connectors across three or more ledgers. The response of an ILQP request only defines one link in the chain.

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

## Get Quote

Quotes are requested with `plugin.sendMessage(message)` and returned via `plugin.on("incoming_message")` (see the Ledger Plugin Interface for more details).
The message formats described here are the `data` properties of an `OutgoingMessage`.

### Request Message Format

| Field    | Type            | Description |
|:---------|:----------------|:------------|
| `method` | String          | `"quote_request"` |
| `id`     | String          | A UUID to match this request to the corresponding response. |
| `data`   | QuoteParameters | An Object describing the quote parameters. |

##### QuoteParameters

| Field                         | Type        | Description |
|:------------------------------|:------------|:------------|
| `source_address`              | ILP Address | Address of the source's account in the source ledger. |
| `destination_address`         | ILP Address | Address of the destination's account in the destination ledger. |
| `source_amount`               | String      | Fixed amount to debit from the source's account. (Required unless `destination_amount` specified.) |
| `destination_amount`          | String      | Fixed amount to credit to the destination's account. (Required unless `source_amount` specified.) |
| `destination_expiry_duration` | String      | (Optional) Number of milliseconds before the transfer in the destination ledger expires. |
| `source_expiry_duration`      | String      | (Optional) Number of milliseconds before the transfer in the source ledger expires. |
| `slippage`                    | String      | (Optional) Custom slippage to assume for the exchange between ledgers, as a decimal proportion. Lower slippage means the payment is cheaper but more likely to fail due to market movement. |

The request must specify either `source_amount` or `destination_amount` but not both.

##### Example request

```js
{
  "method": "quote_request",
  "id": "721e4126-98a1-4974-b35a-8a8f4655f934",
  "data": {
    "source_amount": "100.25",
    "source_address": "example.eur-ledger.alice",
    "destination_address": "example.usd-ledger.bob",
    "source_expiry_duration": "6000",
    "destination_expiry_duration": "5"
  }
}
```

### Response Message Format (success)

| Field    | Type           | Description |
|:---------|:---------------|:------------|
| `method` | String         | `"quote_response"` or `"error"` |
| `id`     | String         | A UUID to match this request to the corresponding `quote_request`. |
| `data`   | Quote or Error | An Object describing the quote (when method=`quote_response`) or the error (when method=`error`). |

##### Quote (method = `"quote_response"`)

| Field                         | Type        | Description |
|:------------------------------|:------------|:------------|
| `source_connector_account`    | ILP Address | The address of the connector's account in the source ledger where it should receive the first transfer. |
| `source_ledger`               | ILP Address | The address of the ILP-enabled ledger where the source account is. |
| `source_amount`               | String      | Decimal number amount of currency the connector's account should receive in the source ledger. |
| `source_expiry_duration`      | String      | Integer number of milliseconds between when the payment in the source ledger is prepared and when it must be executed. |
| `destination_ledger`          | ILP Address | The address of the ILP-enabled ledger where the destination account is. |
| `destination_amount`          | String      | Decimal number amount of currency that should be received by the destination account in the destination ledger. |
| `destination_expiry_duration` | String      | Integer number of milliseconds between when the payment in the destination ledger is prepared and when it must be executed. |

##### Example response (method = `"quote_response"`)

```js
{
  "method": "quote_response",
  "id": "721e4126-98a1-4974-b35a-8a8f4655f934",
  "data": {
    "source_connector_account": "mark",
    "source_ledger": "example.eur-ledger.",
    "source_amount": "100.25",
    "source_expiry_duration": "6000",
    "destination_ledger": "example.usd-ledger.",
    "destination_amount": "105.71",
    "destination_expiry_duration": "5000"
  }
}
```

##### Error (method = `"error"`)

| Field     | Type   | Description |
|:----------|:-------|:------------|
| `id`      | String | The type of error. |
| `message` | String | Additional details about the nature of the error. |

##### Example response (method = `"error"`)

```js
{
  "method": "error",
  "id": "721e4126-98a1-4974-b35a-8a8f4655f934",
  "data": {
    "id": "InvalidBodyError",
    "message": "Missing required parameter: source_address"
  }
}
```

## Next Steps

After getting a quote using ILQP, the client can display the quote to the user and optionally proceed to _Preparing_ (also called _Setting Up_) the payment, for example using the [Simple Payment Setup Protocol](https://github.com/interledger/rfcs/tree/master/0009-simple-payment-setup-protocol). That process actually sets money aside and creates the crypto-conditions that will release the money to the desired parties.

## Appendix A: ASN.1 Module

The [InterledgerQuotingProtocol.asn](InterledgerQuotingProtocol.asn) ASN.1 module tentatively describes the binary version of ILQP. This is not final.
