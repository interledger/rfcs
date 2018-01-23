---
title: The Simple Payment Setup Protocol (SPSP)
draft: 4
---
# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between senders and receivers to facilitate payment over Interledger. SPSP uses the [Pre-Shared Key Version 2 (PSK2)](TODO) transport protocol for condition generation and data encoding.

## Introduction

### Motivation

PSK2 does not specify how payment details, such as the ILP address or shared secret, should be exchanged between the sender and receiver. SPSP is a minimal protocol that uses HTTPS for communicating these details.

### Scope

SPSP provides for exchanging basic receiver details needed by a sender to set up a PSK2 payment. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface for the sender to initiate payments. SPSP clients and receivers use ILP modules to send and receive Interledger payments. SPSP [payment-pointers](#appendix-a-payment-pointer) can be used as a persistent identifier on Interledger. SPSP payment-pointers can also be used as a unique identifier for an invoice to be paid.

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP receiver will run an SPSP server and expose an HTTPS endpoint called the SPSP Endpoint. The sender can query this endpoint to get information about the type of payment that can be made to this receiver. The sender can set up and send multiple ILP payments using the details provided by the receiver.

### Definitions

* **SPSP Client** - The sender application that uses SPSP to interact with the SPSP Server
* **SPSP Server** - The server used on the receiver's side to handle SPSP requests
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP server used for setting up a payment
* **PSK Module** - Software included in the SPSP Client and Server that implements the [Pre-Shared Key Version 2](TODO) protocol.

## Overview

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The sender and receiver use the [Pre-Shared Key Version 2 (PSK2)](TODO) transport protocol to generate the ILP packets. The receiver generates the shared secret and ILP address to be used in PSK2 and communicates it to the sender over HTTPS.

### Model of Operation

We assume that the sender knows the receiver's SPSP endpoint (see [Appendix B: Payment Pointer](#appendix-a-payment-pointer)).

1. The sender's SPSP Client queries the receiver's SPSP Endpoint.
2. The SPSP Endpoint responds with the receiver info, including the receiver's ILP address and the shared secret to be used in PSK2. It MAY respond with a balance associated with this SPSP receiver, i.e. in the case of an invoice.
3. The sender constructs an ILP payment using the receiver's ILP address.
4. The sender begins sending the payment.
  1. The sender uses PSK2 to generate the payment chunk and format additional dthese stepsata intended for the reciever to be sent with the payment.
  2. The sender sends a prepare packet to a connector with the condition and ILP address produced by PSK2.
  3. The receiver's PSK2 module registers the incoming packet, parses, and validates the ILP packet.
  4. The receiver MAY submit the incoming packet to an external system for review to ensure that the funds are wanted.
  5. If the payment is expected, the receiver's PSK2 module derives a fulfillment packet from the prepare packet. If not, the PSK2 module replies with a reject packet.
  6. The receiver MAY update a balance related to this SPSP receiver, i.e. in the case of an invoice.
  7. The fulfillment or rejection packet comes back to the sender.
  8. The sender MAY send further payment chunks with PSK2 (repeating these steps).

## Specification

The SPSP endpoint is a URI used by the sender to query information about the receiver (which may be an invoice) and set up payments. The SPSP endpoint URI MUST NOT contain query string parameters. The sender SHOULD treat the URI as opaque. There are several supported ways to refer to an SPSP endpoint:

- [Payment-pointer](#appendix-a-payment-pointer) (Recommended) `$alice.example.com` or `$example.com/bob`. This SHOULD be the only kind of SPSP identifier exposed to users.
- Raw endpoint URI (Not recommended) `https://example.com/spsp/alice`.

The SPSP Endpoint MUST respond to HTTPS `GET` requests in the following manner:

### Query (`GET <SPSP Endpoint>`)

The sender queries the SPSP endpoint to get information about the type of payment that can be made to this receiver:

#### Request

(With the identifier `$example.com`)

``` http
GET /.well-known/pay HTTP/1.1
Host: example.com
Accept: application/spsp+json
```

#### Response
``` http
HTTP/1.1 200 OK
Content-Type: application/spsp+json

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
Content-Type: application/spsp+json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```

##### Response Headers

The response MUST contain at least the following headers:

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Content-Type`  | MUST be `application/json` to indicates the response is encoded as [JSON](http://www.json.org/). |
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
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific http client in the [Pre-Shared Key protocol](../0016-pre-shared-key/0016-pre-shared-key.md). Should be shared only by the server and this specific http client, and should therefore be different in each query response. |
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
Content-Type: application/json

{
  "id": "InvalidReceiverError",
  "message": "Invalid receiver ID"
}
```

### Payment Setup

The sender uses the receiver details to create the PSK2 payment:

* The `destination_account` should be used as the PSK2 destinationAccount.
* The `shared_secret` should be used as the PSK2 sharedSecret.
* If present, the `balance.maximum` SHOULD be used as the PSK2 chunked payment amount.

In a UI, the `asset_info` and `receiver_info` objects (if present) can be used for display purposes. These objects can be manipulated by the receiver in any way, so amounts SHOULD be displayed in source units when possible.

Note that the sender can send as many PSK2 payments as they want using the same receiver info. The sender SHOULD query the receiver again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.

## Appendix A: Payment Pointer

This is the recommended way to identify an SPSP receiver, and is intended to be the main form of identifier that users on Interledger will interact with. It can be used as a persistent identifier for a person or as a temporary identifier to represent an invoice, much like a bitcoin address.

The payment pointer is in the form `$example.com/bob` (A payment pointer with no path is also acceptable, i.e. `$bob.example.com`). This is converted into an SPSP URI, by removing the `$` and replacing it with `https://`. If the payment pointer has no path, then a path of `/.well-known/pay` is added.

Any characters allowed in a URL are allowed in a payment pointer, but special characters MUST be properly URL-encoded. The payment pointer MUST NOT have any query string, MUST NOT have any authentication info, and MUST NOT have a trailing slash.

Adding this subdomain allows you to use `$example.com` as your payment pointer, even if the actual `example.com` is running a website via a CDN like github pages. The SPSP traffic will go to `spsp.example.com`.

- `$example.com` -> `https://example.com/.well-known/pay`
- `$example.com/bob` -> `https://example.com/bob`
- `$bob.example.com` -> `https://bob.example.com/.well-known/pay`
- `$bob.example.com/invoice/12345` -> `https://bob.example.com/invoice/12345`

With the pointer `$example.com/bob`, the request and response may look like:

```http
GET /bob HTTP 1.1
Host: example.com
Accept: application/spsp+json
```

```http
HTTP/1.1 200 OK
Content-Type: application/spsp+json

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

With the pointer `$bob.example.com`, the request and response may look like the example below. In this example, optional fields have been excluded.

```http
GET /.well-known/pay HTTP 1.1
Host: bob.example.com
Accept: application/spsp+json
```

```http
HTTP/1.1 200 OK
Content-Type: application/spsp+json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```
