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

SPSP provides for exchanging basic receiver details needed by a sender to set up a STREAM payment. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface for the sender to initiate payments. SPSP clients and receivers use ILP modules to send and receive Interledger payments. SPSP [payment-pointers](../0026-payment-pointers/0026-payment-pointers.md) can be used as a persistent identifier on Interledger. SPSP payment-pointers can also be used as a unique identifier for an invoice to be paid.

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP receiver will run an SPSP server and expose an HTTPS endpoint called the SPSP Endpoint. The sender can query this endpoint to get information about the type of payment that can be made to this receiver. The sender can set up and send multiple ILP payments using the details provided by the receiver.

### Definitions

* **SPSP Client** - The sender application that uses SPSP to interact with the SPSP Server
* **SPSP Server** - The server used on the receiver's side to handle SPSP requests
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP server used for setting up a payment
* **STREAM Module** - Software included in the SPSP Client and Server that implements the [STREAM](../0029-stream/0029-stream.md) protocol.

## Overview

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The sender and receiver use the [STREAM](../0029-stream/0029-stream.md) transport protocol to generate the ILP packets. The receiver generates the shared secret and ILP address to be used in STREAM and communicates it to the sender over HTTPS.

### Model of Operation

We assume that the sender knows the receiver's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The sender's SPSP Client queries the receiver's SPSP Endpoint.
2. The SPSP Endpoint responds with the receiver info, including the receiver's ILP address and the shared secret to be used in STREAM. It MAY respond with a balance associated with this SPSP receiver, i.e. in the case of an invoice.
3. The sender constructs an ILP payment using the receiver's ILP address.
4. The sender begins sending the payment.
    1. The sender uses STREAM to establish a ILP/STREAM connection to the receiver.
    2. The sender will construct a stream to the receiver on the ILP/STREAM connection.
    3. The sender will adjust their `sendMax` to reflect the amount they're willing to send.
    4. The receiver will adjust their `receiveMax` to reflect the amount they're willing to receive.
    5. The sender's and receiver's STREAM modules will move as much value as possible while staying inside these bounds.
    6. If the sender reaches their `sendMax`, they end the stream and the connection. If the receiver reaches their `receiveMax`, they will end the STREAM and the connection.

## Specification

The SPSP endpoint is a URI used by the sender to query information about the receiver (which may be an invoice) and set up payments. The SPSP endpoint URI MUST NOT contain query string parameters. The sender SHOULD treat the URI as opaque. There are several supported ways to refer to an SPSP endpoint:

- [Payment-pointer](../0026-payment-pointers/0026-payment-pointers.md) (Recommended) `$alice.example.com` or `$example.com/bob`. This SHOULD be the only kind of SPSP identifier exposed to users.
- Raw endpoint URI (Not recommended) `https://example.com/spsp/alice`. This SHOULD NOT be exposed to users, but SHOULD be supported by SPSP clients.

The SPSP Endpoint MUST respond to HTTPS `GET` requests in the following manner:

### Query (`GET <SPSP Endpoint>`)

The sender queries the SPSP endpoint to get information about the type of payment that can be made to this receiver:

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
| `balance`  | Object | _(OPTIONAL)_ Details of this receiver's balance. Used for invoices and similar temporary accounts. |
| `balance.maximum` | Integer String | Maximum amount, denoted in the minimum divisible units of the receiver's account, which the receiver will accept. This represents the highest sum that incoming chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU). If this is an invoice the `balance.maximum` is the amount at which the invoice would be considered paid. |
| `balance.current` | Integer String | Current sum of all incoming chunks. |
| `asset_info` | Object | _(OPTIONAL)_ Details about the destination asset, for sender's display purposes. |
| `asset_info.code` | String | Asset code to identify the receiver's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. Sender UIs SHOULD be able to render non-standard codes |
| `asset_info.scale` | Integer | The scale of the amounts on the receiver's account (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the receiver's asset/currency) |
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

### Payment Setup

The sender uses the receiver details to create the STREAM connection:

* The `destination_account` should be used as the STREAM destinationAccount.
* The `shared_secret` should be decoded from base64 and used as the STREAM sharedSecret.
* If present, the `balance.maximum - balance.current` SHOULD be used as the STREAM `receiveMax`.

In a UI, the `asset_info` and `receiver_info` objects (if present) can be used for display purposes. These objects can be manipulated by the receiver in any way, so amounts SHOULD be displayed in source units when possible.

Note that the sender can send as many STREAM payments as they want using the same receiver info. The sender SHOULD query the receiver again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.
