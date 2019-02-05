---
title: SPSP Pull Payments
draft: 1
---
# SPSP Pull Payments

## Preface

This document describes how to conduct pull payments via [STREAM](../0029-stream/0029-stream.md) once the payment details have been exchanged via the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP).

## Introduction

### Motivation

The Simple Payment Setup Protocol (SPSP) only descirbes how the details required for a STREAM connection are exchanged. However, it lacks a detailed explaination of how a pull payment is conducted using this connection. 

### Scope

This document specifies basic server details needed by the client to set up a STREAM pull payment. It is intended for use by end-user applications.

### Operation

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about about the server's connection details, namely ILP address and a shared secret, as well as additional information about the type and form of payment that can be made to this server. The client can set up and pull multiple ILP payments using the details provided by the server. 

## Specification

### Query (`GET <SPSP Endpoint>`)

The client queries the SPSP endpoint to get information about the server:

#### Request

``` http
GET /pullagreement456 HTTP/1.1
Host: alice.com
Accept: application/spsp4+json, application/spsp+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "alice.ilpdemo.red~pullagreement456",
  "shared_secret": "k5nubgM6zpb88NPGVnI/tVjRdgpUh+JvMueRFEMvPcY=",
  "balance": {
    "current": "100",
    "maximum": "500"
  },
  "asset_info": {
    "code": "USD",
    "scale": 2
  },
  "frequency_info": { 
    "type": "MONTH",
    "interval": 1
  },
  "timeline_info": {
    "refill_time": "2019-02-10T01:01:13Z",
    "expiry_time": "2019-07-10T01:01:12Z"
  },
  "receiver_info": {
    "name": "XYZ Store",
    "image_url": "https://red.ilpdemo.org/logo.jpg"
  }
}
``` 
More information about the parameters can be found in section [Response Body](#response-body).

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up payments.

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the server. In case of push payments, this is the receiver, in case of pull payments, this is the sender. |
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific HTTP client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific HTTP client, and should therefore be different in each query response. |
| `balance`  | Object | _(OPTIONAL)_ Details of this server account's balance. Used for invoices and and pull payment agreements. |
| `balance.maximum` | Integer String | Maximum amount, denoted in `asset_info.code`, which the client can pull within one frequency interval (see `frequency_info`). It represents the highest sum that outgoing chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU). |
| `balance.current` | Integer String | Amount, denoted in `asset_info.code`, which remains pullable within the current frequency interval (see `frequency_info`). Once `balance.current` equals `0`, the, the client can not pull any more until `balance.current` is refilled on `timeline_info.refill_time`. |
| `asset_info` | Object | _(OPTIONAL)_ Details about the agreement's asset. For pull payment agreements, this is the currency the pull can be made in. |
| `asset_info.code` | String | Asset code to identify the agreement's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `asset_info.scale` | Integer | The scale of the amounts `balance.maximum` and `balance.current` are stated in (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the server's asset/currency) |
| `frequency_info` | Object | Parameters defining the recurrence of pull payments. |
| `frequency_info.type`	| String | Frequency at which `timeline_info.refill_time` is incremented. Possible values are `DAY`, `WEEK`, `MONTH`, `YEAR`. |
| `frequency_info.interval` | Integer | Interval associated with `frequency_info.type`. For example, if `frequency_info.type` is `WEEK` and `frequency_info.interval` is `2`, `balance.current` is refilled every 2 weeks. |
| `timeline_info`	|	Object | Times defining the recurrence of pull payments. |
| `timeline_info.refill_time` |	String | [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) UTC timestamp, e.g. `"2019-02-10T01:01:13Z"`, representing the next time at which `balance.current` will be filled up to the amount of `balance.maximum`. |
| `timeline_info.expiry_time` |	String | _(OPTIONAL)_ [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) UTC timestamp, e.g. `"2019-07-10T01:01:12Z"`, representing the time after which `balance.current` will not be filled up anymore, i.e., when the pull payment agreement expires. |
| `receiver_info` | Object | _(OPTIONAL)_ Arbitrary additional information about the receiver. This field has no schema and the receiver may include any fields they choose. The field names listed below are recommended merely for interoperability purposes. |
| `receiver_info.name` | String | _(OPTIONAL)_ Full name of the individual, company or organization the receiver represents |
| `receiver_info.image_url` | HTTPS URL | _(OPTIONAL)_ URL where the sender can get a picture representation of the receiver |

**Note:** Currency amounts are denominated as integer strings instead of native JSON numbers to avoid losing precision during JSON parsing. Applications MUST represent these numbers in a data type that has precision equal or greater than an unsigned 64-bit integer.

##### Errors

###### receiver Does Not Exist

``` http
HTTP/1.1 404 Not Found
Content-Type: application/spsp4+json

{
  "id": "InvalidReceiverError",
  "message": "Invalid receiver ID"
}
```

## Model of Operation

### Creating a token

**This subsection is not normative but serves as a guideline for how a pull payment token could be created.**

A pull payment token SHOULD be created by the server administrator via a POST request:

#### Request

``` http
POST / HTTP/1.1
Host: alice.com
Accept: application/json
Authorization: Bearer test

{
    "amount": "10000",
    "frequency": "MONTH",
    "interval": "1",
    "cycles": "5",
    "assetCode": "USD",
    "assetScale": "2",
    "secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```

#### Response

``` http
HTTP/1.1 200 OK
Connection: keep-alive
Content-Length: 36
Content-Type: application/json; charset=utf-8
Date: Mon, 04 Feb 2019 23:42:14 GMT
Server: nginx/1.10.1

{
    "token": "$alice.com/pullagreement456"
}
``` 
This token is passed to the client that can use it to conduct the pull payment. The parameters are defined as follows:

| Parameter | Type | Description |
|---|---|---|
| `amount` | Integer String | `balance.maximum` SHOULD be set to this amount. |
| `start` | String | _(OPTIONAL)_ `timeline_info.refill_time` SHOULD be set to this time, unless `start` is in the past, in which case `timeline_info.refill_time` SHOULD be set to `now`. This also holds if `start` is not provided. | |
| `frequency` | String | `frequency_info.type` SHOULD be set to this value.|
| `interval` | Integer String | `frequency_info.interval` SHOULD be set to this value.|
| `cycles` | Integer String | Is used to calculate `timeline_info.expiry_time`, which SHOULD equal `timeline_info.refill_time` + `cycles` * `frequency_info.interval \|\| frequency_info.type`, e.g. `"2019-07-10T01:01:12Z"` = `"2019-02-10T01:01:13Z"` + `5` * `1 MONTH` |
| `assetCode`| String | `asset_info.code` SHOULD be set to this value. |
| `assetScale` | Integer String | `asset_info.scale` SHOULD be set to this value. |
| `secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | Secret that MUST be provided by the client in order to make the pull payment. |

Prior to the creation of the token, the client and server applications MAY negotiate the above defined parameters. This negotiation process is part of the end-user application. 

All requests MUST be exchanged over HTTPS.

### Conducting the pull payment

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP client queries the server's SPSP Endpoint.

2. The SPSP endpoint responds with the server info, including the server's ILP address (`destination_account`) and the shared secret (`shared_secret`) to be used in STREAM. 
    * The `destination_account` SHOULD be used as the STREAM destinationAccount.
    * The `shared_secret` SHOULD be decoded from base64 and used as the STREAM sharedSecret.
  
    It MAY respond with additional information if it is an invoice server (see [SPSP Push Payments](../0035-spsp-push-payments/0035-spsp-push-payments.md)) or a pull payment server. If the amounts within `balance` are negative, the client can push to this endpoint. 

3. The SPSP client establishes a STREAM connection to the server using the server's ILP address and shared secret and constructs a stream to the client on the ILP/STREAM connection.

4. The SPSP server begins sending ILP packets to fulfill the payment.
    1. The server will adjust their `sendMax` to reflect the amount they're willing to send.
        * If present, `balance.current`, converted to the server's uplink currency and padded by a slippage amount, SHOULD be used as the STREAM `sendMax`.
    2. The client will adjust their `receiveMax` to reflect the amount they're willing to receive.
        * If present, `balance.current`, converted to the client's uplink currency, SHOULD be used as the STREAM `receiveMax`.
    3. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    4. If the server reaches their `sendMax`, they end the stream and the connection. If the client reaches their `receiveMax`, they will end the stream and the connection.

Note that the client and server can send as many STREAM payments as they want using the same query response. The client SHOULD query the server again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.
