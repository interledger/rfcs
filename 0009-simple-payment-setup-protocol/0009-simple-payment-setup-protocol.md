---
title: The Simple Payment Setup Protocol (SPSP)
draft: 7
---
# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between counterparties to facilitate payment over Interledger. SPSP uses the [STREAM](../0029-stream/0029-stream.md) transport protocol for condition generation and data encoding.

## Introduction

### Motivation

STREAM does not specify how payment details, such as the ILP address or shared secret, should be exchanged between the counterparties. SPSP is a minimal protocol that uses HTTPS for communicating these details.

### Scope

SPSP provides for exchanging basic server details needed by a client to set up a STREAM connection. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface to initiate payments. SPSP clients and servers use ILP modules to send and receive Interledger payments. SPSP [payment-pointers](../0026-payment-pointers/0026-payment-pointers.md) can be used as a persistent identifier on Interledger. SPSP payment-pointers can also be used as a unique identifier for an invoice to be paid or for a pull payment agreement. 

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about the server's connection details, namely ILP address and a shared secret. The client can use this information to establish a STREAM connection.

### Definitions

* **SPSP Client** - The entity initiating a STREAM connection to the SPSP server
* **SPSP Server** - The entity handling the incoming STREAM connection from the SPSP client
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP Server used for setting up a payment
* **STREAM Module** - Software included in the SPSP client and server that implements the [STREAM](../0029-stream/0029-stream.md) protocol.

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The client and server use the [STREAM](../0029-stream/0029-stream.md) transport protocol to generate the ILP packets. The server generates the shared secret and ILP address to be used in STREAM and communicates it to the client over HTTPS.

## Specification

The SPSP endpoint is a URL the SPSP payment pointer resolves to, used by the client to query information about the server and set up payments. Clients MUST NOT send query string parameters in requests to the SPSP endpoint URL. Servers that receive query string parameters in an SPSP request MUST reject the request with a 400 Bad Request HTTP response code. Clients SHOULD treat the URL as opaque and not depend on any information they derive from the URL.

- [Payment-pointer](../0026-payment-pointers/0026-payment-pointers.md) (Recommended) `$alice.example.com` or `$example.com/bob`. This SHOULD be the only kind of SPSP identifier exposed to users.
- Raw endpoint URL (Not recommended) `https://example.com/spsp/alice`. This SHOULD NOT be exposed to users, but SHOULD be supported by SPSP clients.

The SPSP endpoint MUST respond to HTTPS `GET` requests in the following manner:

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
STREAM-Destination-Account: example.ilpdemo.red.bob
STREAM-Shared-Secret: 6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs=
```

##### Response Headers

The response MUST contain at least the following headers:

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Content-Type`  | MUST be `application/spsp4+json` to indicates the response is encoded as [JSON](http://www.json.org/) and that the ILP payment should be sent via STREAM. |
| `Cache-Control` | Indicates how long the SPSP Client should cache the response. See supported cache-control directives below. |
| `STREAM-Destination-Account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) of the server.|
| `STREAM-Shared-Secret` | The shared secret (32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) including padding) to be used by this specific HTTP client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific HTTP client, and should therefore be different in each query response. |

To handle as many transactions per second as possible, the SPSP client caches results from the SPSP server. The information returned by the SPSP server is not expected to change rapidly, so repeated requests for the same information are usually redundant. The server communicates how long to cache results for using the HTTP-standard [`Cache-Control` header](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Cache-Control) in the responses to RESTful API calls.

The SPSP client understands the following Cache-Control directives:

| Directive     | Description                                                  |
|:--------------|:-------------------------------------------------------------|
| `max-age=<i>` | The client should cache this response for `<i>` seconds. `<i>` MUST be a positive integer |
| `no-cache`    | The client must not cache this response |

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

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP client queries the server's SPSP Endpoint.

2. The SPSP endpoint responds with the server info in the header, namely the server's ILP address (`STREAM-Destination-Account`) and the shared secret (`STREAM-Shared-Secret`) to be used in STREAM. 
    * The `STREAM-Destination-Account` SHOULD be used as the STREAM destinationAccount.
    * The `STREAM-Shared-Secret` SHOULD be decoded from base64 and used as the STREAM sharedSecret.
  
    It MAY respond with additional information in the body if it is an invoice server or a pull payment server. For more information, see [SPSP Push Payments](../0035-spsp-push-payments/0035-spsp-push-payments.md) and [SPSP Pull Payments](../0036-spsp-pull-payments/0036-spsp-pull-payments.md).

3. The SPSP client establishes a STREAM connection to the server using the server's ILP address and shared secret.

Note that the client and server can send as many STREAM payments as they want using the same query response. The client SHOULD query the server again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.
