# Interledger Payment Request (IPR)

## Preface

This document specifies the Interledger Payment Request (IPR) data format. It is intended for use in protocols in which the recipient of an Interledger payment first communicates a request for payment to the sender.

This document provides an example flow to illustrate how IPR could be used in a higher level protocol. This document also details a method for generating Interledger transfer conditions that enable recipients to use the condition as an integrity check on incoming transfers and packets, without maintaining state about all outstanding payment requests.

## Introduction

### Motivation

The Interledger Protocol uses holds based on Crypto Conditions and expiries to ensure a sender's funds are delivered to the destination or returned to the sender's account.

A common approach is for conditions to be generated and fulfilled by the receivers of Interledger transfers. This document specifies one such approach that enables receivers to verify that an incoming transfer matches a payment request they previously created, without the receiver needing to keep a record of all outstanding payment requests.

### Scope

This document defines a suggested format for representing payment requests and an approach for receiver-generated conditions. Protocols built on top of Interledger MAY use the format provided here, though they can use any format they choose instead.

While this document also provides a recommendation for generating transfer conditions, conditions are often opaque to all parties aside from the receiver. Receivers MAY use any condition they choose, however this specification includes best practices that receivers SHOULD take into consideration.

This document does **not** specify how payment requests are communicated from a recipient to a sender.

### Model of Operation

Interledger Payment Requests are intended to be used in higher-level protocols as follows:

1. Recipient creates the payment request and generates the condition using one of algorithms outlined in [Condition Generation](#condition-generation).
2. Recipient communicates the payment request to the sender.
3. Sender generates an ILP Packet from the payment request.
4. Sender prepares a local ledger transfer to a connector, held pending the execution condition given in the payment request and with the ILP Packet attached.
5. Connectors forward the payment until it reaches the recipient.
6. Recipient receives a notification of a held transfer with an ILP Packet attached.
7. Recipient checks the transfer amount against the ILP Packet and checks the payment request has not expired.
8. Recipient regenerates the condition and fulfillment from the ILP Packet attached to the incoming transfer, using the same algorithm as before, and fulfills the transfer's condition. If the condition generated does not match the one in the transfer it means that the ILP Packet has been tampered with and the transfer goes unfulfilled.

## Payment Request Specification

### JSON

```json
{
    "address": "ilpdemo.red.bob.b9c4ceba-51e4-4a80-b1a7-2972383e98af",
    "amount": "10.25",
    "expires_at": "2016-08-16T12:00:00Z",
    "additional_routing_info": {
        "rate_curves": {
            "bitcoin.": [[0,0],[1,400]]
        } 
    },
    "additional_headers": "asdf98zxcvlknannasdpfi09qwoijasdfk09xcv009as7zxcv"
}
```

| Field | Type | Short Description |
|:--|:--|:--|
| `address` | ILP Address | Request-specific address |
| `amount` | Decimal String | Amount requested by the recipient |
| `condition` | Crypto Condition | Execution condition for the payment |
| `expires_at` | [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) Timestamp | Expiry of the request |
| `additional_routing_info` | Object | Details used by the sender's client to route the payment |
| `additional_headers` | Base64 String | Additional headers for the ILP packet |

#### address 

The ILP Address the payment is to be routed to. This SHOULD be a request-specific address in the form `<account address>.<request ID>`, such as `ilpdemo.red.bob.b9c4ceba-51e4-4a80-b1a7-2972383e98af`.

When using the recommended [Condition Generation](#condition-generation) method, account addresses MUST include a request-specific portion to ensure that conditions are unique per-request.

#### amount

The amount requested by the recipient, such as `10.25`, denoted in the assets of the recipient's ledger.

The amount MUST be rounded based on the precision supported by the recipient's ledger.

Recipients SHOULD ignore incoming transfers whose amounts are less than the amount specified in the payment request. Recipients MAY ignore incoming transfers whose amounts are greater than requested.

#### condition

The Crypto Condition to be used as the execution condition for the payment. See [Condition Generation](#condition-generation) for recommendations the recipient MAY use for creating the condition.

#### expires_at

The timestamp when the request expires. Recipients SHOULD NOT fulfill the conditions of incoming transfers that arrive after the expiry has passed. Senders MAY use the request expiry to determine the expiry of the transfer they put on hold for the first connector.

#### additional_routing_info

Additional information supplied by the recipient for the sender's client to route the payment. For example, this may include the rate curve that includes fee and exchange rate information for payments from a well-known ledger to the recipient's ledgers.

#### additional_headers

Additional binary headers, encoded as a base64 string, that should be included in the ILP Packet. The sender SHOULD treat these as opaque.

### Binary

**TODO**

## Condition Generation

It is RECOMMENDED that recipients use a Message Authentication Code (MAC) of the details of their payment request in the condition so that the condition can be used as an integrity check on incoming transfers. This allows a recipient to ensure that a transfer matches a request they previously generated, without the recipient needing to maintain a log of all outstanding payment requests.

Recipients MUST include a payment request-specific component in the account ILP Address to ensure that conditions are unique per-request.

### Preimage Condition from JSON

This is how a [PREIMAGE-SHA-256 Crypto Condition](../0002-crypto-conditions) MAY be generated using an HMAC of a JSON-encoded Interledger Payment Request:

1. The recipient takes the `address`, `amount`, and `expires_at` fields from the payment request. Any fields that are used for routing are probably not important to perform an integrity check upon, because they may be modified in transit and there is no further use for them once the ILP packet is received attached to an incoming transfer.
2. The recipient uses a canonical encoding, such as [Canonical JSON](https://www.npmjs.com/package/canonical-json) to create a stringified version of `1.`
3. The recipient uses a secret key to create an HMAC of `2.`
4. The recipient uses the digest of `3.` as the preimage of a [PREIMAGE-SHA-256 Crypto Condition](../0002-crypto-conditions).

The following snippet shows how this can be done in JavaScript:

```js
const crypto = require('crypto') // Node.js crypto
const stringify = require('canonical-json') // https://www.npmjs.com/package/canonical-json
const cc = require('cc') // https://www.npmjs.com/package/five-bells-condition

const RECIPIENT_HMAC_KEY = Buffer.from('/4t65RDqth7/rxI0j+MqtQyv04Y8mzUCMhAAofhDQIY=', 'base64')
const requestString = stringify({
  "address": "ilpdemo.red.bob.b9c4ceba-51e4-4a80-b1a7-2972383e98af",
  "amount": "10.25",
  "expires_at": "2016-08-16T12:00:00Z"
})

const hmac = crypto.createHmac('sha256', RECIPIENT_HMAC_KEY)
hmac.update(requestString)
const cryptoCondition = new cc.PreimageSha256()
cryptoCondition.setPreimage(hmac.digest())

const condition = cryptoCondition.getConditionUri()
const fulfillment = cryptoCondition.serializeUri()
```
