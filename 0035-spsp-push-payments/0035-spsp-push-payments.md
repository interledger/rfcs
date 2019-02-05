---
title: SPSP Push Payments
draft: 1
---
# SPSP Push Payments

## Preface

This document describes how to conduct push payments via [STREAM](../0029-stream/0029-stream.md) once the payment details have been exchanged via the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP).

## Introduction

### Motivation

The Simple Payment Setup Protocol (SPSP) only descirbes how the details required for a STREAM connection are exchanged. However, it lacks a detailed explaination of how a push payment is conducted using this connection. 

### Scope

This document specifies basic server details needed by the client to set up a STREAM push payment. It is intended for use by end-user applications.

### Operation

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about about the server's connection details, namely ILP address and a shared secret, as well as additional information about the type and form of payment that can be made to this server. The client can set up and send multiple ILP payments using the details provided by the server. 

## Specification

### Query (`GET <SPSP Endpoint>`)

The client queries the SPSP endpoint to get information about the server:

#### Request

(With the identifier `$example.com`)

``` http
GET /.well-known/pay HTTP/1.1
Host: example.com
Accept: application/spsp4+json, application/spsp+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```

In case of an invoice SPSP server, it may respond with additional information.

#### Request

``` http
GET /invoice123 HTTP/1.1
Host: example.com
Accept: application/spsp4+json, application/spsp+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red~invoice123",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs=",
  "balance": {
    "maximum": "-10000",
    "current": "-5360"
  },
  "asset_info": {
    "code": "USD",
    "scale": 2
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
| `balance`  | Object | _(OPTIONAL)_ Details of this server account's balance. |
| `balance.maximum` | Integer String | Negative of the maximum amount, denoted in `asset_info.code`, which the server will accept. It represents the highest sum that incoming chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU). If an invoice amounts to 100 USD, `balance.maximum` is `-10000`, given that `asset_info.code` is `USD` and `asset_info.scale` is `2`. |
| `balance.current` | Integer String | Negative of the amount, denoted in `asset_info.code`, which is still outstanding, i.e., it is equal to `\|balance.maximum\|` minus the sum of all incoming chunks. Once `balance.current` equals `0`, the invoice is considered to be paid. |
| `asset_info` | Object | _(OPTIONAL)_ Details about the agreement's asset. For invoices, this is the currency the invoice is stated in. |
| `asset_info.code` | String | Asset code to identify the agreement's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `asset_info.scale` | Integer | The scale of the amounts `balance.maximum` and `balance.current` are stated in (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the server's asset/currency) |
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

### Conducting the push payment

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP client queries the server's SPSP Endpoint.

2. The SPSP endpoint responds with the server info, including the server's ILP address (`destination_account`) and the shared secret (`shared_secret`) to be used in STREAM. 
    * The `destination_account` SHOULD be used as the STREAM destinationAccount.
    * The `shared_secret` SHOULD be decoded from base64 and used as the STREAM sharedSecret.
  
    It MAY respond with additional information if it is an invoice server or a pull payment server (see [SPSP Pull Payments](../0036-spsp-pull-payments/0036-spsp-pull-payments.md)). If there is no `balance` field or the amounts within `balance` are negative, the client can push to this endpoint.  

3. The SPSP client establishes a STREAM connection to the server using the server's ILP address and shared secret and constructs a stream to the server on the ILP/STREAM connection.

4. The SPSP client begins sending ILP packets to fulfill the payment.
    1. The client will adjust their `sendMax` to reflect the amount they're willing to send.
        * If present, `\|balance.current\|` SHOULD be used as the STREAM `sendMax`.
    2. The server will adjust their `receiveMax` to reflect the amount they're willing to receive.
        * If present, `\|balance.current\|` SHOULD be used as the STREAM `receiveMax`.
    3. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    4. If the client reaches their `sendMax`, they end the stream and the connection. If the server reaches their `receiveMax`, they will end the stream and the connection.

Note that the client and server can send as many STREAM payments as they want using the same query response. The client SHOULD query the server again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.
