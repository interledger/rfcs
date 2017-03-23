# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between senders and receivers to set up an Interledger payment. SPSP uses the [Pre-Shared Key (PSK)](../0016-pre-shared-key/0016-pre-shared-key.md) transport protocol for condition generation and data encoding.

## Introduction

### Motivation

The Interledger Protocol does not specify how payment details, such as the ILP Packet or Crypto Condition, should be exchanged between the sender and receiver. SPSP is a minimal protocol that uses HTTPS for communicating these details.

### Scope

SPSP provides for exchanging basic receiver details needed by a sender to set up an ILP payment. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface for the sender to initiate payments. SPSP clients and receivers use ILP modules to send and receive Interledger payments.

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP receiver will run an SPSP server and expose an HTTPS endpoint called the SPSP Endpoint. The sender can query this endpoint to get information about the type of payment that can be made to this receiver. The sender can set up and send multiple ILP payments using the details provided by the receiver.

### Definitions

* **SPSP Client** - The sender application that uses SPSP to interact with the SPSP Server
* **SPSP Server** - The server used on the receiver's side to handle SPSP requests
* **SPSP Endpoint** - The specific HTTPS endpoint on the SPSP server used for setting up a payment
* **PSK Module** - Software included in the SPSP Client and Server that implements the [Pre-Shared Key](../0016-pre-shared-key/0016-pre-shared-key.md) protocol

## Overview

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. The sender and receiver use the [Pre-Shared Key (PSK)](../0016-pre-shared-key/0016-pre-shared-key.md) transport protocol to generate the condition and fulfillment. The receiver generates the shared secret to be used in PSK and communicates it to the sender over HTTPS.

### Model of Operation

We assume that the sender knows the receiver's SPSP endpoint (see [Appendix A: (Optional) Webfinger Discovery](#appendix-a-optional-webfinger-discovery)).

1. The sender's SPSP Client queries the receiver's SPSP Endpoint.
2. The SPSP Endpoint responds with the receiver info, including the receiver's ILP address and the shared secret to be used in PSK.
3. The sender constructs an ILP payment using the receiver's ILP address.
4. The sender uses PSK to generate the payment condition and format additional data intended for the reciever to be sent with the payment.
5. The sender prepares a local transfer to a connector with the condition and ILP packet attached.
6. The receiver's PSK module registers the incoming transfer, parses and validates the ILP packet and the incoming transfer.
7. The receiver MAY submit the incoming payment to an external system for review to ensure that the funds are wanted.
8. If the payment is expected, the receiver's PSK module submits the condition fulfillment to the ledger to execute the transfer. If not, the PSK module rejects the incoming transfer.
9. If the receiver executed the transfer, the sender's SPSP client receives a notification from its ILP module that the transfer has been executed, including the condition fulfillment from the receiver, and notifies the sender that the payment is completed. If the receiver rejected the transfer, the sender's SPSP client receives a notification with the receiver-specified error message detailing why the payment was rejected.

## Specification

The SPSP endpoint is a URI used by the sender to query information about the sender and set up payments. The SPSP endpoint URI MAY contain query string parameters. The sender SHOULD treat the URI as opaque.

The SPSP Endpoint MUST respond to HTTPS `GET` requests in the following manner:

### Query (`GET <SPSP Endpoint>`)

The sender queries the SPSP endpoint to get information about the type of payment that can be made to this receiver:

#### Request
``` http
GET /api/spsp/bob HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json
```

#### Response
``` http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "destination_account": "example.ilpdemo.red.bob",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C-YB5X9FhSOUPCL_5nha5Vs",
  "maximum_destination_amount": "100000",
  "minimum_destination_amount": "10",
  "ledger_info": {
    "currency_code": "USD",
    "currency_symbol": "$",
    "scale": 2,
    "precision": 10
  },
  "receiver_info": {
    "name": "Bob Dylan",
    "image_url": "https://red.ilpdemo.org/api/spsp/bob/profile_pic.jpg"
  }
}
```

[Try this request](https://red.ilpdemo.org/api/receivers/bob)

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
| `shared_secret` | 32 bytes, [base64-url encoded](https://en.wikipedia.org/wiki/Base64#URL_applications) | The shared secret to be used in the [Pre-Shared Key protocol](../0016-pre-shared-key/0016-pre-shared-key.md) |
| `maximum_destination_amount` | Integer String | Maximum amount, denoted in the minimum divisible units of the ledger, the receiver will accept. This amount may be determined by the ledger's maximum account balance or transfer amount. If the receiver expects a specific amount to be delivered, this may be set equal to the `minimum_destination_amount` |
| `minimum_destination_amount` | Integer String | Minimum amount, denoted in the minimum divisible units of the ledger, the receiver will accept. This amount may be determined by the minimum transfer amount of the ledger. If the receiver expects a specific amounts to be delivered, this may be set equal to the `maximum_destination_amount` |
| `ledger_info` | Object | Details about the destination ledger |
| `ledger_info.currency_code` | String | Currency code to identify the receiver's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. Sender UIs SHOULD be able to render non-standard codes |
| `ledger_info.currency_symbol` | String | Symbol for the receiver's currency intended for display in the sender's UI (e.g. `"$"` or `"shares"`). Sender UIs SHOULD be able to render non-standard symbols |
| `ledger_info.scale` | Integer | The scale of the amounts on the destination ledger (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the destination ledger's currency) |
| `ledger_info.precision` | Integer | The maximum precision supported by the ledger |
| `receiver_info` | Object | Arbitrary additional information about the receiver. This field has no schema and the receiver may include any fields they choose. The field names listed below are recommended merely for interoperability purposes. |
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

The sender uses the receiver details to create the ILP packet:

* The `account` in the ILP packet is the `destination_account` provided by the receiver
* The `amount` is determined by the sender:

    * The sender uses the `ledger_info.scale` to determine the integer amount to include in the ILP packet (e.g. if they want the receiver to receive 10 units on their ledger, a `ledger_info.scale` value of 2 would indicate they should set the `amount` to 1000). In cases where the sender knows the integer amount the receiver should get, for example if that amount was requested by the receiver out of band, the sender does not need to use the `ledger_info.scale`
    * The sender SHOULD NOT set an amount greater than the `maximum_destination_amount` or lower than the `minimum_destination_amount`, as this will be rejected by the receiver
    * The sender SHOULD NOT set an amount with a precision greater than the `ledger_info.precision`, as this will be rejected by the destination ledger

* The `data` is encoded using the [Pre-Shared Key protocol](../0016-pre-shared-key/0016-pre-shared-key.md):

    * The key is the `shared_secret` provided by the receiver
    * Additional data may be included in the PSK details. SPSP data MUST be JSON.
    * Private PSK headers SHOULD include `Content-Type: application/json` and `Content-Length: <byte length of data>`

Note that the sender can send as many payments as they want using the same receiver info. The sender SHOULD query the receiver again once the time indicated in the [`Cache-Control` header](#response-headers) has passed.

## Appendix A: (Optional) Webfinger Discovery

Whenever possible, receiver URLs should be exchanged out-of-band and discovery should be skipped. However, in some cases, it may be useful to have a standardized user-friendly identifier. This discovery method describes how to resolve such an identifier to an SPSP endpoint.

First, the sender uses Webfinger ([RFC 7033](https://tools.ietf.org/html/rfc7033)) to look up an identifier (e.g. `bob@red.ilpdemo.org`):

``` http
GET /.well-known/webfinger?resource=acct%3Abob%40red.ilpdemo.org HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json
```
``` http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "subject": "acct:bob@red.ilpdemo.org",
  "links": [
    {
      "rel": "https://interledger.org/rel/spsp/v2",
      "href": "https://red.ilpdemo.org/api/spsp/bob"
    }
  ]
}
```
[Try this request](https://red.ilpdemo.org/.well-known/webfinger?resource=acct%3Abob%40red.ilpdemo.org)

