---
title: SPSP Pull Payments
draft: 1
---
# SPSP Pull Payments

## Preface

This document describes how to conduct Pull Payments via [STREAM](../0029-stream/0029-stream.md) once the payment details have been exchanged via the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP).

## Introduction

### Pull Payments
In contrast to a push payment, where the Payer (sender) actively sends (pushes) units of value to the Payee (receiver), Pull Payments shift the active part from the Payer to the Payee. With the Payer's consent, the Payee can pull units of value directly from the Payer's account to their own account. The only active engagement of the Payer is required during the negotiation phase of the Pull Payment Agreement. 

### Motivation

The [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP) only describes how the details required for a STREAM connection are exchanged and how a simple push payment is made. However, it lacks a detailed explanation of how a Pull Payment is conducted using this connection. 

### Scope

This document specifies how to conduct a Pull Payment once a STREAM connection has been set up. It is intended for wallet providers and merchants.

### Definitions
* **Payer** - The entity that units of value are pulled from by the Payee. It is running the [SPSP Server](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions).
* **Payee** - The entity that is pulling units of value from the Payer. It is running the [SPSP Client](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions).
* **Pull Payment** - The process of pulling units of value from one account into another account.
* **Pull Payment Agreement** - An agreement between the Payer and the Payee that specifies how much value can be pulled how often and for how long. 
* **Pull Payment Pointer** - A [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md) that includes a unique and opaque string and represents a Pull Payment Agreement. The SPSP Client uses it to query the [SPSP Endpoint](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions) on the SPSP Server. 

### Operation Overview

The Payee's SPSP Client will set up a [STREAM](../0029-stream/0029-stream.md) connection to the Payer's SPSP Server using the Pull Payment Pointer, as described by the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md). On connection, the SPSP Client tries to pull value from the SPSP server, staying within the terms of the Pull Payment Agreement.

## Model of Operation

### Negotiating the Pull Payment Agreement

Prior to a Pull Payment, the Payer and the Payee have to negotiate a Pull Payment Agreement. This agreement SHOULD be comprised of the parameters defined in the `agreement`-object within the [Response Body](#Response-Body). The Payer's SPSP Server SHOULD store the negotiated Pull Payment Agreement parameters.

The result of the negotiation is a Pull Payment Pointer representing the Pull Payment Agreement. The Pull Payment Pointer is required by the Payee's SPSP Client to connect to the Payer's SPSP server. 

Implementations MAY try to parse the Pull Payment Pointer, however, it MUST support totally opaque Pull Payment Pointers. 

### Conducting the Pull Payment

The Payee's SPSP Client opens a [STREAM](../0029-stream/0029-stream.md) connection to the Payer's SPSP Server as described in the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md). 

Once this connection is established, the process continues as follows: 

The SPSP Server begins sending ILP packets to complete the Pull Payment.
  1. The SPSP Server will adjust their `sendMax` to reflect the amount they're willing to send.
      * `sendMax` SHOULD be derived from the Pull Payment Agreement parameters, i.e., `sendMax` SHOULD be equal to `pull.balance.available`, converted to the SPSP Server's operating asset, taking exchange rate fluctuations into account.
  2. The SPSP Client will adjust their `receiveMax` to reflect the amount they're willing to receive.
      * `receiveMax` MAY be `Infinity`.
  3. The SPSP Client's and Server's [STREAM Modules](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions) will move as much value as possible while staying inside these bounds.
  4. If the SPSP Server reaches their `sendMax`, they end the stream and the connection. If the SPSP Client reaches their `receiveMax`, they will end the stream and the connection.

The STREAM parameters - `sendMax` and `receiveMax` - are defined in [STREAM's frame encoding](../0029-stream/0029-stream.md#53-frames).

Note that if there are multiple open streams (via one or more STREAM connections) to the `destination_account` the Pull Payment Pointer is resolving to, the SPSP Server MUST only set one `sendMax` at a time.

## Specification

### Query (`GET <SPSP Endpoint>`)

The SPSP Client queries the SPSP Endpoint to get information about the SPSP Server:

#### Request

``` http
GET /0f09dc92-84ad-401b-a7c9-441bc6173f4e HTTP/1.1
Host: alice.com
Accept: application/spsp4+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "alice.ilpdemo.red.0f09dc92-84ad-401b-a7c9-441bc6173f4e",
  "shared_secret": "k5nubgM6zpb88NPGVnI/tVjRdgpUh+JvMueRFEMvPcY=",
  "pull": {
    "balance": {
      "total": "5000",
      "interval": "1000",
      "available": "1000"
    },
    "cycle": 3,
    "agreement": {
      "amount": "2000",
      "start": "2019-01-01T08:00Z",
      "expiry": "2021-01-02T00:00Z", 
      "interval": "P0Y1M0DT0H0M0S",
      "cycles": 12,
      "cap": false,
      "asset": {
        "code": "USD",
        "scale": 2
      }
    }
  }
}
``` 

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up a STREAM connection as well as optional parameters for displaying purposes. The fields are defined in the following: 

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | (see [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Response-Body)) |
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | (see [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Response-Body)) |
| `pull`  | Object | _(OPTIONAL)_ Details of this Pull Payment Pointer. |
| `pull.balance`  | Object | _(OPTIONAL)_ Details of this Pull Payment Pointer's balance. |
| `pull.balance.total` | Integer String | _(OPTIONAL)_ Total amount, denoted in `pull.agreement.asset.code`, which has been pulled by the client since `pull.agreement.start` to date. It is the sum of all outgoing chunks. |
| `pull.balance.interval` | Integer String | _(OPTIONAL)_ Amount, denoted in `pull.agreement.asset.code`, which has been pulled by the client since the start of the current `pull.cycle`. It is the sum of all outgoing chunks. |
| `pull.balance.available` | Integer String | _(OPTIONAL)_ Amount, denoted in `pull.agreement.asset.code`, which is still available to be pulled by the client until the end of the current `pull.agreement.cycle`. |
| `pull.cycle` | Integer | _(OPTIONAL)_ Current interval cycle out of a total of `pull.agreement.cycles`. |
| `pull.agreement` | Object | _(OPTIONAL)_ Details of the Pull Payment Agreement. |
| `pull.agreement.amount` | Integer String | _(OPTIONAL)_ Amount, denoted in `pull.agreement.asset.code`, which can pulled by the client each `pull.agreement.interval`. |
| `pull.agreement.start` |	String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) UTC timestamp, e.g. `"2019-01-01T08:00Z"`, representing the start of the Pull Payment Agreement. |
| `pull.agreement.expiry` |	String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) UTC timestamp, e.g. `"2021-01-02T00:00Z"`, representing the expiry of the Pull Payment Agreement. It is the time when the SPSP endpoint is destroyed, i.e. remaining funds cannot be pulled after that point in time. |
| `pull.agreement.interval` | String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) duration, e.g. `"P0Y1M0DT0H0M0S"` = 1 month, which describes how often `pull.agreement.amount` can be pulled. |
| `pull.agreement.cycles` | Integer | _(OPTIONAL)_ Number of times that `pull.agreement.interval` is applied, starting at `pull.agreement.start`. If `pull.agreement.interval` is 1 month and `pull.agreement.cycles` is 12, then `pull.agreement.amount` can be pulled 12 times within the year starting at `pull.agreement.start`. |
| `pull.agreement.cap` | Boolean | _(OPTONAL)_ Defines whether any balance not pulled before the start of the next interval cycle is accumulated or expires. If `pull.agreement.cap = true`, the maximum pullable amount per `pull.agreement.interval` is `pull.agreement.amount`. If `pull.agreement.cap = false`, the maximum pullable amount per `pull.agreement.interval` is `pull.agreement.amount` plus any remaining funds accumulated but not pulled over the last interval cycles.|
| `pull.agreement.asset` | Object | _(OPTIONAL)_ Details of the agreement's asset. |
| `pull.agreement.asset.code` | String |  _(OPTIONAL)_ Asset code to identify the agreement's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `pull.agreement.asset.scale` | Integer |  _(OPTIONAL)_ The scale of the amounts `pull.balance.total`, `pull.balance.interval`, and `pull.balance.available` are stated in (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the server's asset/currency) |

**Note:** Currency amounts are denominated as integer strings instead of native JSON numbers to avoid losing precision during JSON parsing. Applications MUST represent these numbers in a data type that has precision equal or greater than an unsigned 64-bit integer.

##### Errors

###### Pointer Does Not Exist

``` http
HTTP/1.1 404 Not Found
Content-Type: application/spsp4+json

{
  "id": "InvalidPointerError",
  "message": "Pointer does not exist."
}
```
