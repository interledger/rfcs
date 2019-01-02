---
title: The Simple Payment Setup Protocol (SPSP)
draft: 6
---
# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between senders and receivers to facilitate payment over Interledger. SPSP uses the [STREAM](../0029-stream/0029-stream.md) transport protocol for condition generation and data encoding.

## Introduction

### Motivation

STREAM does not specify how payment details, such as the ILP address or shared secret, should be exchanged between the sender and receiver. SPSP is a minimal protocol that uses HTTPS for communicating these details.

### Scope

SPSP provides for exchanging basic server details needed by a client to set up a STREAM payment. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface for the sender to initiate payments. SPSP clients and receivers use ILP modules to send and receive Interledger payments. SPSP [payment-pointers](../0026-payment-pointers/0026-payment-pointers.md) can be used as a persistent identifier on Interledger. SPSP payment-pointers can also be used as a unique identifier for an invoice to be paid, or, in the case of pull payments, as a token that specifies the terms and conditions for such a pull.

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about the type of payment that can be made to or pulled from this server. The client can set up and send or pull multiple ILP payments using the details provided by the server.

### Definitions

* **SPSP Client** - The application that uses SPSP to interact with the SPSP Server
* **SPSP Server** - The server used to handle SPSP requests
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP server used for setting up a payment
* **STREAM Module** - Software included in the SPSP Client and Server that implements the [STREAM](../0029-stream/0029-stream.md) protocol.

## Overview

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The client and server use the [STREAM](../0029-stream/0029-stream.md) transport protocol to generate the ILP packets. The server generates the shared secret and ILP address to be used in STREAM and communicates it to the client over HTTPS.

### Model of Operation

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP Client queries the server's SPSP Endpoint.
2. The SPSP Endpoint responds with the server info, including the servers's ILP address and the shared secret to be used in STREAM. It MAY respond with additional information if it is an invoice server or a pull payment server.

In case of simple push payments or invoices, the process continues as follows:

3. The client constructs an ILP payment using the server's ILP address.
4. The client begins sending the payment.
    1. The client uses STREAM to establish a ILP/STREAM connection to the server.
    2. The client will construct a stream to the server on the ILP/STREAM connection.
    3. The client will adjust their `sendMax` to reflect the amount they're willing to send.
    4. The server will adjust their `receiveMax` to reflect the amount they're willing to receive.
    5. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    6. If the client reaches their `sendMax`, they end the stream and the connection. If the server reaches their `receiveMax`, they will end the STREAM and the connection.

In case of pull payments, the process continues as follows:

3. The client establishes a STREAM connection to the server using the server's ILP address.
4. The server begins sending the payment.
    1. The server will construct a stream to the client on the ILP/STREAM connection.
    2. The server will adjust their `sendMax` to reflect the amount they're willing to send.
    3. The client will adjust their `receiveMax` to reflect the amount they're willing to receive.
    4. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    5. If the server reaches their `sendMax`, they end the stream and the connection. If the client reaches their `receiveMax`, they will end the STREAM and the connection.

## Specification

The SPSP endpoint is a URI used by the client to query information about the server (which may be an invoice or a pull payment token) and set up payments. The SPSP endpoint URI MUST NOT contain query string parameters. The sender SHOULD treat the URI as opaque. There are several supported ways to refer to an SPSP endpoint:

- [Payment-pointer](../0026-payment-pointers/0026-payment-pointers.md) (Recommended) `$alice.example.com` or `$example.com/bob`. This SHOULD be the only kind of SPSP identifier exposed to users.
- Raw endpoint URI (Not recommended) `https://example.com/spsp/alice`. This SHOULD NOT be exposed to users, but SHOULD be supported by SPSP clients.

The SPSP Endpoint MUST respond to HTTPS `GET` requests in the following manner:

### Query (`GET <SPSP Endpoint>`)

The client queries the SPSP endpoint to get information about the type of payment that can be made to this server:

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
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs=",
  "balance": {
    "maximum": "100000",
    "current": "5360"
  },
  "asset_info": {
    "code": "USD",
    "scale": 2
  },
  "receiver_info": {
    "name": "Bob Dylan",
    "image_url": "https://red.ilpdemo.org/api/spsp/bob/profile_pic.jpg"
  }
}
```

The `balance`, `asset_info`, and `receiver_info` objects are all optional,
so a minimal SPSP response looks like:

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```

In case of a pull payment server, it is possible to request the the payment token via

``` http
GET /f8095a44-c77f-4414-a19d-7aeca03f17c7 HTTP/1.1
Host: example.com
Accept: application/spsp4+json, application/spsp+json
```

and receive the response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red~f8095a44-c77f-4414-a19d-7aeca03f17c7",
  "sharedSecret": "b88NPGVk5nubgM6zpnI/tVjRdgpUh+JvMueRFEMvPcY=",
  "balance": {
    "amount": "100",
    "current": "100",
    "maximum": "10000"
  },
  "receiverInfo": {
    "name": "Amazon",
    "interval": "7",
    "cooldown": "1546037535"
  }
}
``` 

##### Response Headers

The response MUST contain at least the following headers:

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Content-Type`  | MUST be `application/spsp4+json` to indicates the response is encoded as [JSON](http://www.json.org/) and that the ILP payment should be sent via STREAM. |
| `Cache-Control` | Indicates how long the SPSP Client should cache the response. See supported cache-control directives below. |

To handle as many transactions per second as possible, the SPSP Client caches results from the SPSP Server. The information returned by the SPSP Server is not expected to change rapidly, so repeated requests for the same information are usually redundant. The server communicates how long to cache results for using the HTTP-standard [`Cache-Control` header](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Cache-Control) in the responses to RESTful API calls.

The SPSP Client understands the following Cache-Control directives:

| Directive     | Description                                                  |
|:--------------|:-------------------------------------------------------------|
| `max-age=<i>` | The client should cache this response for `<i>` seconds. `<i>` MUST be a positive integer |
| `no-cache`    | The client must not cache this response |

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up payments.

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the receiver's account |
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific http client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific http client, and should therefore be different in each query response. |
| `balance`  | Object | _(OPTIONAL)_ Details of this server account's balance. Used for invoices and pull payments as well as similar temporary accounts. |
| `balance.maximum` | Integer String | Maximum amount, denoted in the minimum divisible units of the server's account, which the server will accept or be willing to send. This represents the highest sum that incoming or outgoing chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU). If this is an invoice the `balance.maximum` is the amount at which the invoice would be considered paid. If this is a pull payment token, `balance.maximum` is the maximum amount that can be pulled in total.|
| `balance.current` | Integer String | Current sum of all incoming or outgoing chunks. |
| `balance.amount` | Integer String | Amount that can be pulled within a certain time frame. |
| `asset_info` | Object | _(OPTIONAL)_ Details about the destination asset, for sender's display purposes. |
| `asset_info.code` | String | Asset code to identify the receiver's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. Sender UIs SHOULD be able to render non-standard codes |
| `asset_info.scale` | Integer | The scale of the amounts on the receiver's account (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the receiver's asset/currency) |
| `receiver_info` | Object | _(OPTIONAL)_ Arbitrary additional information about the receiver or token. In case of push payments, this field has no schema and the receiver may include any fields they choose. In case of pull payments, `receiver_info.interval` and `receiver_info.cooldown` will be returned. |
| `receiver_info.name` | String | _(OPTIONAL)_ Full name of the individual, company or organization the receiver represents |
| `receiver_info.image_url` | HTTPS URL | _(OPTIONAL)_ URL where the sender can get a picture representation of the receiver |
| `receiver_info.interval` | Integer String | Number of days the client is not allowed to pull from the server, i.e. the cooldown period. |
| `receiver_info.cooldown` | Integer String | Timestamp indicating when the cooldown period is over. |

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

### Push Payment Setup

The client uses the server's details to create the STREAM connection:

* The `destination_account` should be used as the STREAM destinationAccount.
* The `shared_secret` should be decoded from base64 and used as the STREAM sharedSecret.
* If present, the `balance.maximum - balance.current` SHOULD be used as the STREAM `receiveMax`.

In a UI, the `asset_info` and `receiver_info` objects (if present) can be used for display purposes. These objects can be manipulated by the receiver in any way, so amounts SHOULD be displayed in source units when possible.

Note that the sender can send as many STREAM payments as they want using the same receiver info. The sender SHOULD query the receiver again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.

### Pull Payment Setup

The client uses the server's details to create the STREAM connection:

* The `destination_account` should be used as the STREAM destinationAccount.
* The `shared_secret` should be decoded from base64 and used as the STREAM sharedSecret.
* The `balance.amount` SHOULD be used as the STREAM `receiveMax`.
* The `balance.current` MUST NOT be bigger than `balance.maximum`.
* The `receiver_info.cooldown` MUST be increased by `receiver_info.interval` whenever a pull payment was conducted and MUST be exceeded before the next payment can be pulled. 