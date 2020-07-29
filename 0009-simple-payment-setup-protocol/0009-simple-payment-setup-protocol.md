---
title: The Simple Payment Setup Protocol (SPSP)
type: working-draft
draft: 12
---
# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between payee and payer to facilitate payment over Interledger. SPSP uses the [STREAM](../0029-stream/0029-stream.md) transport protocol for condition generation and data encoding.

## Introduction

### Motivation

STREAM does not specify how payment details, such as the ILP address or shared secret, should be exchanged between the counterparties. SPSP is a minimal protocol that uses HTTPS for communicating these details.

### Scope

SPSP provides for exchanging basic server details needed by a client to set up a STREAM connection. It is intended for use by end-user applications.

### Definitions

* **SPSP Client** - The application that uses SPSP to interact with the SPSP Server.
* **SPSP Server** - The application that handles incoming SPSP requests from the SPSP Client.
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP Server used for setting up a payment.
* **STREAM Module** - Software included in the SPSP Client and Server that implements the [STREAM](../0029-stream/0029-stream.md) protocol.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface to initiate payments. SPSP Clients and Servers use the STREAM Module to send and receive Interledger payments. [Payment pointers](../0026-payment-pointers/0026-payment-pointers.md) can be used as a persistent identifier on Interledger. Payment pointers can also be used as a unique identifier for an invoice to be paid or for a pull payment agreement. 

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP Server will expose an HTTPS endpoint called the SPSP Endpoint. The SPSP Client can query this endpoint to get information about the SPSP Server's connection details, namely the ILP address and a shared secret. The SPSP Client can apply this information to establish a STREAM connection using the STREAM Module.

### Relation to Other Protocols

SPSP is used for exchanging connection information before an ILP payment or data transfer is initiated. The SPSP Client and Server use the [STREAM](../0029-stream/0029-stream.md) transport protocol to generate the ILP packets. The SPSP Server generates the shared secret and ILP address to be used in STREAM and communicates it to the client over HTTPS.

## Specification

The SPSP Endpoint is a URL the payment pointer resolves to, used by the SPSP Client to query information about the SPSP Server and set up payments. SPSP Clients SHOULD treat the URL as opaque and not depend on any information they derive from the URL. There are several supported ways to refer to an SPSP Endpoint:

- [Payment pointer](../0026-payment-pointers/0026-payment-pointers.md) (Recommended) `$alice.example.com` or `$example.com/bob`. This SHOULD be the only kind of SPSP identifier exposed to users.
- Raw endpoint URL (Not recommended) `https://example.com/spsp/alice`. This SHOULD NOT be exposed to users, but SHOULD be supported by SPSP Clients.

The SPSP Endpoint MUST respond to HTTPS `GET` requests in the following manner:

### Query (`GET <SPSP Endpoint>`)

The client queries the SPSP Endpoint to get information about the server:

#### Request

(With the identifier `$example.com`)

``` http
GET /.well-known/pay HTTP/1.1
Host: example.com
Accept: application/spsp4+json, application/spsp+json
```

##### Request Headers to Support Web Monetization Polyfills

[Web Monetization](../0028-web-monetization/0028-web-monetization.md) polyfills may query SPSP from a non-privileged context if they are implemented as a script rather than a browser extension. Sites may choose to use a script-based polyfill to enable Web Monetization for their visitors without requiring any browser extension or browser support.

In this situation, [CORS](https://developer.mozilla.org/en-US/docs/Web/HTTP/CORS) headers are necessary to make the SPSP server reachable. If CORS headers are not included, the SPSP query will be rejected and Web Monetization will fail to initialize.

SPSP servers SHOULD expose the CORS headers listed below on `GET <SPSP Endpoint>` **and `OPTIONS <SPSP Endpoint>`**.

| Header | Value |
|:---|:---|
| `Access-Control-Allow-Origin` | `*` |
| `Access-Control-Allow-Headers` | `web-monetization-id` |

##### Request Headers to Support STREAM Receipts

The request MAY contain at least the following headers in order to pre-share [STREAM Receipt](../0039-stream-receipts/0039-stream-receipts.md) details between the SPSP Server and [receipt verifier](../0039-stream-receipts/0039-stream-receipts.md#conventions-and-definitions):

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Receipt-Nonce`  | A base64-encoded Receipt Nonce. |
| `Receipt-Secret` | A base64-encoded Receipt Secret. |

The SPSP Client MAY be provided with an SPSP Endpoint belonging to the receipt verifier, which would add the receipt headers and proxy the query to the SPSP Server.

#### Response
``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs=",
  "receipts_enabled": true
}
```
More information about the parameters can be found in section [Response Body](#response-body).

##### Response Headers

The response MUST contain at least the following headers:

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Content-Type`  | MUST be `application/spsp4+json` to indicate the response is encoded as [JSON](http://www.json.org/) and that the ILP payment should be sent via STREAM. |
| `Cache-Control` | Indicates how long the SPSP Client should cache the response. See supported cache-control directives below. |

To handle as many transactions per second as possible, the SPSP Client caches results from the SPSP Server. The information returned by the SPSP Server is not expected to change rapidly, so repeated requests for the same information are usually redundant. The SPSP Server communicates how long to cache results for using the HTTP-standard [`Cache-Control` header](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Cache-Control) in the responses to RESTful API calls.

The SPSP Client understands the following Cache-Control directives:

| Directive     | Description                                                  |
|:--------------|:-------------------------------------------------------------|
| `max-age=<i>` | The SPSP Client should cache this response for `<i>` seconds. `<i>` MUST be a positive integer. |
| `no-cache`    | The SPSP Client must not cache this response. |

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up payments. More fields can be added but implementations MUST ignore fields they do not understand. 

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the SPSP Server. In case of push payments, this is the receiver. In case of pull payments, this is the sender. |
| `shared_secret` | 32 bytes, [base64 (base64url) encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific HTTP client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific HTTP client, and should therefore be different in each query response. Even though clients SHOULD accept base64url encoded secrets, base64 encoded secrets are recommended. |
| `receipts_enabled` | Boolean | _(OPTIONAL)_  If `true`, the SPSP server will issue STREAM Receipts in the STREAM connection. If `false` or omitted, the server will not issue STREAM Receipts. |

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

### Establishing a connection

We assume that the SPSP Client knows the SPSP Server's SPSP Endpoint (see [Payment pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP Client queries the SPSP Server's SPSP Endpoint.

2. The SPSP Endpoint responds with the SPSP Server's info, namely the ILP address (`destination_account`) and the shared secret (`shared_secret`) to be used in STREAM. 
    * The `destination_account` MUST be used as the STREAM `destinationAccount`.
    * The `shared_secret` MUST be decoded from base64 and used as the STREAM `sharedSecret`.
  
    It MAY respond with additional information if it is an invoice server or a pull payment server. For more information, see [SPSP Invoices](../0037-spsp-invoices/0037-spsp-invoices.md) and [SPSP Pull Payments](../0036-spsp-pull-payments/0036-spsp-pull-payments.md).

3. The SPSP Client establishes a STREAM connection to the SPSP Server using the SPSP Server's ILP address and shared secret.

### Examples

#### Simple push payment

Given the open STREAM connection, the SPSP Client begins sending ILP packets of value.
  1. The SPSP Client will adjust their STREAM `sendMax` to reflect the amount they're willing to send.
  2. The SPSP Server will adjust their STREAM `receiveMax` to reflect the amount they're willing to receive.
  3. The SPSP Client's and Server's STREAM Modules will move as much value as possible while staying inside these bounds.
  4. If the SPSP Client reaches their `sendMax`, they end the stream and the connection. If the SPSP Server reaches their `receiveMax`, they will end the stream and the connection.

#### Simple data transmission

Given the open STREAM connection, either the SPSP Client or the Server begins sending ILP packets of data.

The size of the data SHOULD be defined by setting STREAM `maxOffset`. Each application built on STREAM and using the principle of data transmission MAY define more restrictive requirements. 

---

All STREAM parameters - `destinationAccount`, `sharedSecret`, `sendMax`, `receiveMax`, `maxOffset` - are defined in [STREAM's frame encoding](../0029-stream/0029-stream.md#53-frames).

Note that the SPSP Client and Server can send as many STREAM payments and data as they want using the same query response. If the STREAM connection is closed the Client SHOULD attempt to reconnect with the same parameters or it SHOULD query the Server again for new connection parameters once the time indicated in the [`Cache-Control` header](#response-headers) has passed.
