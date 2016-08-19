# Simple Payment Setup Protocol (SPSP)

## Preface

This document describes the Simple Payment Setup Protocol (SPSP), a basic protocol for exchanging payment information between senders and recipients to set up an Interledger payment.

## Introduction 

### Motivation

The Interledger Protocol does not specify how payment details, such as the ILP Packet or Crypto Condition, should be exchanged between the sender and recipient. SPSP is a minimal protocol that uses HTTP for communicating these details.

### Scope

SPSP provides for exchanging basic payment details needed by a sender to confirm the details of and set up an ILP payment. It is intended for use by end-user applications.

### Interfaces

SPSP may be used by end-user applications, such as a digital wallet with a user interface for the sender to initiate payments. SPSP clients and receivers use ILP modules to send and receive Interledger payments.

SPSP messages MUST be exchanged over HTTPS.

### Operation

Any SPSP recipient will create a receiving HTTP endpoint called the *receiver*. The sender can query this endpoint to get information about the type of payment that can be made to this receiver. The sender also uses the receiver endpoint to set up the ILP payment.

### Definitions

#### SPSP Client

The sender application that uses SPSP to interact with the SPSP Server.

#### SPSP Server

The server used on the recipient's side to handle SPSP requests.

#### Receiver

The specific HTTP endpoint on the SPSP used for setting up a payment.

## Overview

### Relation to Other Protocols

SPSP is used for exchanging payment information before an ILP payment is initiated. It uses the receiver generated [Interledger Payment Requests](../0011-interledger-payment-request) over HTTP.

### Model of Operation

#### Fixed Destination Amount

SPSP may be used by the sender to send a payment such that the recipient receives a specific amount of their chosen currency or asset type. The model of operation is illustrated with the following example:

We assume that the sender knows the receiver endpoint (see [Appendix A: (Optional) Webfinger Discovery](#appendix-a-optional-webfinger-discovery)).

1. The sender's SPSP client queries the receiver endpoint.
2. The receiver endpoint responds with the receiver info, including the receiver's currency code.
3. The sender chooses an amount of the receiver's asset to deliver.
4. The sender's SPSP client submits the payment information, including the destination amount, to the receiver endpoint.
5. The receiver endpoint responds with an [Interledger Payment Request](../0011-interledger-payment-request), which includes the execution condition.
6. The sender's SPSP client uses its ILP module to get a quote in their currency or asset type for the ILP transfer.
7. The sender accepts the quote.
8. The sender's SPSP client uses its ILP module to initiate the ILP payment.
9. The receiver's ILP module registers the incoming transfer held pending the fulfillment of the Crypto Condition. It validates that the transfer matches the packet and regenerates the condition fulfillment using the method recommended in the [Interledger Payment Request](../0011-interledger-payment-request) spec. The ILP module submits the fulfillment to execute the transfer and claim the funds.
10. The sender's SPSP client receives a notification from its ILP module that the transfer has been executed, including the condition fulfillment from the recipient, and notifies the sender that the payment is completed.

#### Fixed Source Amount

SPSP may be used by the sender to send a payment of a fixed amount of the sender's chosen currency or asset type. This is illustrated with the following example:

We assume that the sender knows the receiver endpoint (see [Appendix A: (Optional) Webfinger Discovery](#appendix-a-optional-webfinger-discovery)).

1. The sender's SPSP client queries the receiver endpoint.
2. The receiver endpoint responds with the receiver info, including the recipient's ILP address.
3. The sender choses an amount of their currency or assets to send.
4. The sender's SPSP client uses its ILP module to quote how much of the recipient's currency or asset type will be delivered to the recipient's ILP address for the given source amount.
5. The sender accepts the quote.
6. The sender's SPSP client submits the payment information, including the destination amount, to the receiver endpoint.
7. The receiver endpoint responds with an [Interledger Payment Requests](../0011-interledger-payment-request), which includes the execution condition.
8. The sender's SPSP client uses its ILP module to create a transfer **using the chosen source amount, NOT by quoting the payment request**, and attaches the ILP packet to the transfer.
9. The receiver's ILP module registers the incoming transfer held pending the fulfillment of the Crypto Condition. It validates that the transfer matches the packet and regenerates the condition fulfillment using the method recommended in the [Interledger Payment Request](../0011-interledger-payment-request) spec. The ILP module submits the fulfillment to execute the transfer and claim the funds.
10. The sender's SPSP client receives a notification from its ILP module that the transfer has been executed, including the condition fulfillment from the recipient, and notifies the sender that the payment is completed.

#### Invoice

1. The sender's SPSP client queries the receiver endpoint.
2. The receiver endpoint responds with the receiver info, including the invoice status, amount, and currency code.
3. The sender's SPSP client submits the sender's info, including the sender's ILP address to the receiver endpoint.
4. The receiver endpoint responds with an [Interledger Payment Request](../0011-interledger-payment-request) corresponding to the destination amount.
5. The sender's SPSP client uses its ILP module to get a quote in their currency or asset type for the ILP transfer.
6. The sender accepts the quote.
7. The sender's SPSP client uses its ILP module to initiate the ILP transfer.
8. The receiver's ILP module registers the incoming transfer held pending the fulfillment of the Crypto Condition. It validates that the transfer matches the packet and regenerates the condition fulfillment using the method recommended in the [Interledger Payment Request](../0011-interledger-payment-request) spec. The ILP module submits the fulfillment to execute the transfer and claim the funds.
9. The sender's SPSP client receives a notification from its ILP module that the transfer has been executed, including the condition fulfillment from the recipient, and notifies the sender that the payment is completed.

## Specification

The receiver endpoint is a URI used by the sender to query information about the sender and set up payments. The receiver URI MAY contain query string parameters. The sender SHOULD treat the URI as opaque.

The receiver endpoint MUST respond to HTTP `GET` and `POST` requests in the following manner:

### Query (`GET <receiver>`)

The sender queries the receiver endpoint to get information about the type of payment that can be made to this receiver:

#### Request
``` http
GET /api/receivers/bob HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json
```

#### Response
``` http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "type": "payee",
  "account": "ilpdemo.red.bob",
  "currency_code": "USD",
  "currency_symbol": "$",
  "name": "Bob Dylan",
  "image_url": "https://red.ilpdemo.org/api/receivers/bob/profile_pic.jpg"
}
```

[Try this request](https://red.ilpdemo.org/api/receivers/bob)

Possible values for `type` are:

`payee`
: This is a general receiving account for peer-to-peer payments.

`invoice`
: This is an invoice, meaning it can be paid only once and only with a specific amount.

##### Payee

Payee information consists of basic account details. Amounts are chosen by the sender.

Example Receiver:
``` json
{
  "type": "payee",
  "account": "ilpdemo.red.bob",
  "currency_code": "USD",
  "currency_symbol": "$",
  "name": "Bob Dylan",
  "image_url": "https://red.ilpdemo.org/api/receivers/bob/profile_pic.jpg"
}
```

| Field | Type | Description |
|---|---|---|
| `type` | `"payee"` | Receiver type |
| `account` | ILP Address | ILP Address of the recipient's account |
| `currency_code` | String | Currency code to identify the receiver's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. Sender UIs SHOULD be able to render non-standard codes |
| `currency_symbol` | String | Symbol for the receiver's currency intended for display in the sender's UI (e.g. `"$"` or `"shares"`). Sender UIs SHOULD be able to render non-standard symbols |
| `name` | String | Full name of the individual, company or organization the receiver represents |
| `image_url` | HTTPS URL | URL that a picture of the recipient can be fetched from. The image MUST be square and SHOULD be 128x128 pixels. |

If this receiver is not available, an error can be generated at this stage:

``` http
HTTP/1.1 404 Not Found
Content-Type: application/json

{
  "id": "InvalidReceiverIdError",
  "message": "Invalid receiver ID"
}
```

##### Invoice

Invoice information includes an exact amount as well as the status of the invoice. (Invoices can only be paid once.)

Example Receiver:
``` json
{
  "type": "invoice",
  "account": "ilpdemo.red.amazon.111-7777777-1111111",
  "currency_code": "USD",
  "currency_symbol": "$",
  "amount": "10.40",
  "status": "unpaid",
  "invoice_info": "https://www.amazon.com/gp/your-account/order-details?ie=UTF8&orderID=111-7777777-1111111"
}
```

| Field | Type | Description |
|---|---|---|
| `type` | `"invoice"` | Receiver type |
| `account` | ILP Address | ILP Address of the recipient's account |
| `currency_code` | String | Currency code to identify the receiver's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. Sender UIs SHOULD be able to render non-standard codes |
| `currency_symbol` | String | Symbol for the receiver's currency intended for display in the sender's UI (e.g. `"$"` or `"shares"`). Sender UIs SHOULD be able to render non-standard symbols |
| `amount` | Decimal String | Value of the invoice in the recipient's currency |
| `status` | Enum: `"paid"`, `"unpaid"`, `"cancelled"` | State of the invoice |
| `invoice_info` | URI | URI where additional information about the invoice can be found. |

### Setup (`POST <receiver>`)

When the sender is ready to make a payment, it submits a payment object to the receiver.

#### Request

##### For a Payee

``` http
POST /api/receiver/bob HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json

{
  "amount": "10.40",
  "sender_identifier": "alice@blue.ilpdemo.org",
  "memo": "Hey Bob!"
}
```

| Field | Type | Description |
|---|---|---|
| `amount` | Decimal String | _Destination amount_ the receiver will receive |
| `sender_identifier` | String | Identifier of the sender |
| `memo` | String | Message for the recipient linked to the payment |

##### For an Invoice

``` http
POST /api/receiver/bob HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json

{
  "sender_identifier": "alice@blue.ilpdemo.org"
}
```

| Field | Type | Description |
|---|---|---|
| `sender_identifier` | String | Identifier of the sender |

#### Response
``` http
HTTP/1.1 201 Created
Content-Type: application/json

{
    "address": "ilpdemo.red.bob.b9c4ceba-51e4-4a80-b1a7-2972383e98af",
    "amount": "10.40",
    "expires_at": "2016-08-16T12:00:00Z",
    "data": {
        "sender_identifier": "alice@blue.ilpdemo.org"
    },
    "additional_headers": "asdf98zxcvlknannasdpfi09qwoijasdfk09xcv009as7zxcv",
    "condition": "cc:0:3:wey2IMPk-3MsBpbOcObIbtgIMs0f7uBMGwebg1qUeyw:32"
}
```
The response is an [Interledger Payment Request](../0011-interledger-payment-request).

The setup is what primes the receiver to expect the incoming payment. The receiver generates the payment request and condition the sender must use to create the ILP Packet. The fulfillment of the condition will serve as the sender's proof of payment.

The receiver has the opportunity to reject an incoming payment before any funds move, for instance because of daily limits:

``` http
HTTP/1.1 422 Unprocessable Entity
Content-Type: application/json

{
  "id": "LimitExceededError",
  "error": "Daily incoming funds limit exceeded"
}
```

## Appendix A: (Optional) Webfinger Discovery

Whenever possible, receiver URLs should be exchanged out-of-band and discovery should be skipped. However, in some cases, it may be useful to have a standardized user-friendly identifier. This discovery method describes how to resolve such an identifier to an SPSP receiver endpoint.

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
      "rel": "https://interledger.org/rel/receiver",
      "href": "https://red.ilpdemo.org/api/receivers/bob"
    }
  ]
}
```
[Try this request](https://red.ilpdemo.org/.well-known/webfinger?resource=acct%3Abob%40red.ilpdemo.org)

