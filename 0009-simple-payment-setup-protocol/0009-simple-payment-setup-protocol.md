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

Any SPSP server will expose an HTTPS endpoint called the SPSP Endpoint. The client can query this endpoint to get information about the type of payment that can be made to or pulled from this server. The client can use this information to establish a STREAM connection and begin sending or receiving payments.

### Definitions

* **SPSP Client** - The entity initiating a STREAM connection to the SPSP server
* **SPSP Server** - The entity handling the incoming STREAM connection from the SPSP client
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP Server used for setting up a payment
* **STREAM Module** - Software included in the SPSP client and server that implements the [STREAM](../0029-stream/0029-stream.md) protocol.

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The client and server use the [STREAM](../0029-stream/0029-stream.md) transport protocol to generate the ILP packets. The server generates the shared secret and ILP address to be used in STREAM and communicates it to the client over HTTPS.

## Specification

The SPSP endpoint is a URL the SPSP payment pointer resolves to, used by the client to query information about the server (which may return an invoice or a pull payment agreement) and set up payments. Clients MUST NOT send query string parameters in requests to the SPSP endpoint URL. Servers that receive query string parameters in an SPSP request MUST reject the request with a 400 Bad Request HTTP response code. Clients SHOULD treat the URL as opaque and not depend on any information they derive from the URL.

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

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs="
}
```

Invoice and pull payment SPSP enpoints will make use of optional fields. A response from an invoice endpoint may look like this:

``` http
GET /invoice123 HTTP/1.1
Host: example.com
Accept: application/spsp4+json, application/spsp+json

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

whereas a pull payment endpoint will respond with the specs of the agreement, i.e.:

``` http
GET /pullagreement456 HTTP/1.1
Host: alice.com
Accept: application/spsp4+json, application/spsp+json

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

##### Response Headers

The response MUST contain at least the following headers:

| Header          | Description                                                |
|:----------------|:-----------------------------------------------------------|
| `Content-Type`  | MUST be `application/spsp4+json` to indicates the response is encoded as [JSON](http://www.json.org/) and that the ILP payment should be sent via STREAM. |
| `Cache-Control` | Indicates how long the SPSP Client should cache the response. See supported cache-control directives below. |

To handle as many transactions per second as possible, the SPSP client caches results from the SPSP server. The information returned by the SPSP server is not expected to change rapidly, so repeated requests for the same information are usually redundant. The server communicates how long to cache results for using the HTTP-standard [`Cache-Control` header](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Cache-Control) in the responses to RESTful API calls.

The SPSP client understands the following Cache-Control directives:

| Directive     | Description                                                  |
|:--------------|:-------------------------------------------------------------|
| `max-age=<i>` | The client should cache this response for `<i>` seconds. `<i>` MUST be a positive integer |
| `no-cache`    | The client must not cache this response |

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up payments.

| Field | Type | Description |
|---|---|---|
| `destination_account` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the server. In case of push payments, this is the receiver, in case of pull payments, this is the sender. |
| `shared_secret` | 32 bytes, [base64 encoded](https://en.wikipedia.org/wiki/Base64) (including padding) | The shared secret to be used by this specific HTTP client in the [STREAM](../0029-stream/0029-stream.md). Should be shared only by the server and this specific HTTP client, and should therefore be different in each query response. |
| `balance`  | Object | _(OPTIONAL)_ Details of this server account's balance. Used for invoices and and pull payment agreements. |
| `balance.maximum` | Integer String | <ul><li>**Invoice**: Negative of the maximum amount, denoted in `asset_info.code`, which the server will accept. It represents the highest sum that incoming chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU). If an invoice amount is 100 USD, `balance.maximum` is `-10000`, given that `asset_info.code` is `USD` and `asset_info.scale` is `2`.</li><li>**Pull payment agreement**: Maximum amount, denoted in `asset_info.code`, which the client can pull within one frequency interval (see `frequency_info`). It represents the highest sum that outgoing chunks are allowed to reach, not the highest size of an individual chunk (which is determined by path MTU).</li></ul> |
| `balance.current` | Integer String | <ul><li>**Invoice**: Negative of the amount, denoted in `asset_info.code`, which is still outstanding, i.e., it is equal to `\|balance.maximum\|` minus the sum of all incoming chunks. Once `balance.current` equals `0`, the invoice is considered to be paid.</li><li>**Pull payment agreement**: Amount, denoted in `asset_info.code`, which remains pullable within the current frequency interval (see `frequency_info`). Once `balance.current` equals `0`, the, the client can not pull any more until `balance.current` is refilled on `timeline_info.refill_time`.</li></ul> |
| `asset_info` | Object | _(OPTIONAL)_ Details about the agreement's asset. For invoices, this is the currency the invoice is stated in. For pull payment agreements, this is the currency the pull can be made in. |
| `asset_info.code` | String | Asset code to identify the agreement's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `asset_info.scale` | Integer | The scale of the amounts `balance.maximum` and `balance.current` are stated in (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the server's asset/currency) |
| `frequency_info` | Object | _(OPTIONAL)_ Parameters defining the recurrence of pull payments. |
| `frequency_info.type`	| String | Frequency at which `timeline_info.refill_time` is incremented. Possible values are `DAY`, `WEEK`, `MONTH`, `YEAR`. |
| `frequency_info.interval` | Integer | Interval associated with `frequency_info.type`. For example, if `frequency_info.type` is `WEEK` and `frequency_info.interval` is `2`, `balance.current` is refilled every 2 weeks. |
| `timeline_info`	|	Object | _(OPTIONAL)_ Times defining the recurrence of pull payments. |
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

We assume that the client knows the server's SPSP endpoint (see [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md)).

1. The user's SPSP client queries the server's SPSP Endpoint.

2. The SPSP endpoint responds with the server info, including the servers's ILP address (`destination_account`) and the shared secret (`shared_secret`) to be used in STREAM. 
    * The `destination_account` SHOULD be used as the STREAM destinationAccount.
    * The `shared_secret` SHOULD be decoded from base64 and used as the STREAM sharedSecret.
  
    It MAY respond with additional information if it is an invoice server or a pull payment server. If the amounts within `balance` are negative, the client can push to this endpoint. If the amounts within `balance` are positive, the client can pull from this endpoint. If `balance` is not provided, only push payments are possible. 

3. The SPSP client establishes a STREAM connection to the server using the server's ILP address and shared secret.

In case of push payments or invoices, the process continues as follows:

4. The SPSP client begins sending ILP packets to fulfill the payment.
    1. The client will construct a stream to the server on the ILP/STREAM connection.
    2. The client will adjust their `sendMax` to reflect the amount they're willing to send.
        * If present, `|balance.current|` SHOULD be used as the STREAM `sendMax`.
    3. The server will adjust their `receiveMax` to reflect the amount they're willing to receive.
        * If present, `|balance.current|` SHOULD be used as the STREAM `receiveMax`.
    4. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    5. If the client reaches their `sendMax`, they end the stream and the connection. If the server reaches their `receiveMax`, they will end the stream and the connection.

In case of pull payments, the process continues as follows:

4. The SPSP server begins sending ILP packets to fulfill the payment.
    1. The server will construct a stream to the client on the ILP/STREAM connection.
    2. The server will adjust their `sendMax` to reflect the amount they're willing to send.
        * If present, `|balance.current|` SHOULD be used as the STREAM `sendMax`.
    3. The client will adjust their `receiveMax` to reflect the amount they're willing to receive.
        * If present, `|balance.current|` SHOULD be used as the STREAM `receiveMax`.
    4. The client's and server's STREAM modules will move as much value as possible while staying inside these bounds.
    5. If the server reaches their `sendMax`, they end the stream and the connection. If the client reaches their `receiveMax`, they will end the stream and the connection.

Note that the client and server can send as many STREAM payments as they want using the same query response. The client SHOULD query the server again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.