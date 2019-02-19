---
title: SPSP Pull Payments
draft: 1
---
# SPSP Pull Payments

## Preface

This document describes how to conduct pull payments via [STREAM](../0029-stream/0029-stream.md) once the payment details have been exchanged via the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP).

## Introduction

### Motivation

The Simple Payment Setup Protocol (SPSP) only descirbes how the details required for a STREAM connection are exchanged and how a simple push payment is made. However, it lacks a detailed explaination of how a pull payment is conducted using this connection. 

### Scope

This document specifies how to conduct a pull payment once a STREAM connection has been set up. It is intended for use by end-user applications.

### Operation Overview

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about about the server's connection details, namely ILP address and a shared secret. The endpoint MAY also contain additional information for displaying purposes. The client can set up a STREAM connection and pull multiple ILP payments using the details provided by the server. 

## Model of Operation

### Creating a token

A pull payment token SHOULD be be opaque. For the purpose of offline generation, it MAY include negotiated pull payment agreement parameters that SHOULD become obsolete once the SPSP endpoint corresponding to that token has been created. The SPSP server SHOULD store the negotiated pull payment agreement parameters.

The pull payment agreement parameters that SHOULD be negotiated are those defined in the `agreement` object within the [Response Body](#Response-Body). 

### Conducting the pull payment

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP client queries the server's SPSP Endpoint.

2. The SPSP endpoint responds with the server info, including the server's ILP address (`destination_account`) and the shared secret (`shared_secret`) to be used in STREAM. 
    * The `destination_account` SHOULD be used as the STREAM destinationAccount.
    * The `shared_secret` SHOULD be decoded from base64 and used as the STREAM sharedSecret.

3. The SPSP client establishes a STREAM connection to the server using the server's ILP address and shared secret and constructs a stream to the client on the ILP/STREAM connection.

4. The SPSP server begins sending ILP packets to fulfill the payment.
    1. The server will adjust their `sendMax` to reflect the amount they're willing to send.
        * `sendMax` SHOULD be derived from the pull payment agreement parameters.
    2. The client will adjust their `receiveMax` to reflect the amount they're willing to receive.
        * `receiveMax` MAY be `Infinity`.
    3. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    4. If the server reaches their `sendMax`, they end the stream and the connection. If the client reaches their `receiveMax`, they will end the stream and the connection.

## Specification

### Query (`GET <SPSP Endpoint>`)

The client queries the SPSP endpoint to get information about the server:

#### Request

``` http
GET /0f09dc92-84ad-401b-a7c9-441bc6173f4e HTTP/1.1
Host: alice.com
Accept: application/spsp4+json, application/spsp+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "alice.ilpdemo.red~0f09dc92-84ad-401b-a7c9-441bc6173f4e",
  "shared_secret": "k5nubgM6zpb88NPGVnI/tVjRdgpUh+JvMueRFEMvPcY=",
  "balance": {
    "total": "5000",
    "interval": "1000",
    "available": "1000"
  },
  "cycle": 3,
  "agreement": {
    "amount": "2000",
    "start": "2019-01-01T08:00Z",
    "interval": "P0Y1M0DT0H0M0S",
    "cycles": 12,
    "cap": false,
    "asset": {
      "code": "USD",
      "scale": 2
    }
  }
}
``` 

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up a STREAM connection as well as optional parameters for displaying purposes.

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the server. In case of push payments, this is the receiver, in case of pull payments, this is the sender. |
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific HTTP client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific HTTP client, and should therefore be different in each query response. |
| `balance`  | Object | _(OPTIONAL)_ Details of this server account's balance. |
| `balance.total` | Integer String | _(OPTIONAL)_ Total amount, denoted in `agreement.asset.code`, which has been pulled by the client since `start` to date. It is the sum of all outgoing chunks. |
| `balance.interval` | Integer String | _(OPTIONAL)_ Amount, denoted in `agreement.asset.code`, which has been pulled by the client since the start of the current `cycle`. It is the sum of all outgoing chunks. |
| `balance.available` | Integer String | _(OPTIONAL)_ Amount, denoted in `agreement.asset.code`, which is still available to be pulled by the client until the end of the current `cycle`. |
| `cycle` | Integer | _(OPTIONAL)_ Current interval cycle out of a total of `agreement.cycles`. |
| `agreement` | Object | _(OPTIONAL)_ Details about the pull payment agreement. |
| `agreement.amount` | Integer String | _(OPTIONAL)_ Amount, denoted in `agreement.asset.code`, which can pulled by the client each `agreement.interval`. |
| `agreement.start` |	String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) UTC timestamp, e.g. `"2019-02-10T01:01:13Z"`, representing the start of the pull payment agreement. |
| `agreement.interval` | String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) duration, e.g. `"P0Y1M0DT0H0M0S"` = 1 month, which describes how often `agreement.amount` can be pulled. |
| `agreement.cycles` | Integer | _(OPTIONAL)_ Number of times that `agreement.interval` is applied, starting at `agreement.start`. If `agreement.interval` is 1 month and `agreement.cycles` is 12, then `agreement.amount` can be pulled 12 times within the year starting at `agreement.start`. |
| `agreement.cap` | Boolean | _(OPTONAL)_ Defines whether any balance not pulled before the start of the next interval cycle is accumulated or expires. If `agreement.cap = true`, the maximum pullable amount per `agreement.interval` is `agreement.amount`. If `agreement.cap = false`, the maximum pullable amount per `agreement.interval` is `agreement.amount` plus any remaining funds accumulated but not pulled over the last interval cycles.|
| `agreement.asset` | Object | _(OPTIONAL)_ Details about the agreement's asset. |
| `agreement.asset.code` | String |  _(OPTIONAL)_ Asset code to identify the agreement's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `agreement.asset.scale` | Integer |  _(OPTIONAL)_ The scale of the amounts `balance.maximum` and `balance.current` are stated in (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the server's asset/currency) |

**Note:** Currency amounts are denominated as integer strings instead of native JSON numbers to avoid losing precision during JSON parsing. Applications MUST represent these numbers in a data type that has precision equal or greater than an unsigned 64-bit integer.

##### Errors

###### Token Does Not Exist

``` http
HTTP/1.1 404 Not Found
Content-Type: application/spsp4+json

{
  "id": "InvalidPointerError",
  "message": "Token does not exist."
}
```
