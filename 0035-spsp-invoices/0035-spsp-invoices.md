---
title: SPSP Invoices
draft: 1
---
# SPSP Invoices

## Preface

This document describes how conduct an Invoice Payment via [STREAM](../0029-stream/0029-stream.md) once the payment details have been exchanged via the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP).

## Introduction

### Invoice Payments

An Invoice Payment is a push payment to an Invoice SPSP Endpoint that allows the Payer (sender) to settle outstanding balances with the Payee (receiver). The Invoice SPSP Endpoint MAY expose the details about the Invoice and, when receiving value, updates its outstanding balance accordingly.

### Motivation

The [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) (SPSP) only descirbes how the details required for a STREAM connection are exchanged and how simple push payments are made. Invoices require the SPSP server to keep track of incoming payments, i.e. act as an accounting server. 

### Scope

This document specifies Invoice specific endpoints on SPSP and payments to these. They are intended for use by end-user applications.

### Definitions
* **Invoice** - A set of parameters describing the nature of the value transfer as well as its terms and status.
* **Invoice Payment** - The process of completing an Invoice by transfering value to its corresponding Invoice SPSP Endpoint.
* **Payer** - The entity that is sending units of value to an Invoice SPSP Endpoint on the Payee's [SPSP Server](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions). It is running the [SPSP Client](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions).
* **Payee** - The entity that is creating an Invoice SPSP Endpoint and receives units of value from the Payer using this Invoice SPSP Endpoint. It is running the [SPSP Server](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions).
* **Invoice SPSP Endpoint** - A specific [SPSP Endpoint](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions) that MAY expose the details of the invoice and receives units of value from the Payer. It is the means by which the Payee keeps track of incoming payments. 

### Operation Overview

The Payer's SPSP Client will set up a [STREAM](../0029-stream/0029-stream.md) connection to the Payee's SPSP Server using the [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md) resolving to the Invoice SPSP Endpoint, as described by the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md). On connection, the SPSP Client pushes as much value to the SPSP Server as necessary to complete the Invoice.

## Model of Operation

### Creating an Invoice SPSP Endpoint

Prior to the Invoice Payment, the Payee has to create the Invoice SPSP Endpoint on the SPSP Server, which is represented by a [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md). This Payment Pointer MUST contain an ID representing the Invoice. The Payee's SPSP Server SHOULD store the Invoice details, which are defined in the `invoice`-object within the [Response Body](#Response-Body), within the Invoice SPSP Endpoint in order to account for balance changes.

### Conducting an Invoice Payment

The Payer's SPSP Client opens a [STREAM](../0029-stream/0029-stream.md) connection to the Payee's SPSP Server as described in the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md). Once this connection is established, the process continues as follows: 

The SPSP Client begins sending ILP packets to complete the Invoice.
  1. The SPSP Client will adjust their `sendMax` to reflect the amount they're willing to send.
      * `sendMax` SHOULD be derived from the Invoice.
  2. The SPSP Server will adjust their `receiveMax` to reflect the amount they're willing to receive.
      * `receiveMax` SHOULD be derived from the Invoice.
  3. The SPSP Client's and Server's [STREAM Modules](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Definitions) will move as much value as possible while staying inside these bounds.
  4. If the SPSP Client reaches their `sendMax`, they end the stream and the connection. If the SPSP Server reaches their `receiveMax`, they will end the stream and the connection.

The STREAM parameters - `sendMax` and `receiveMax` - are defined in [STREAM's frame encoding](../0029-stream/0029-stream.md#53-frames).


## Specification

### Query (`GET <SPSP Endpoint>`)

The SPSP Client queries the Invoice SPSP Endpoint to get information about the SPSP Server as well as Invoice specific details:

#### Request

``` http
GET /invoice123 HTTP/1.1
Host: example.com
Accept: application/spsp4+json
```

#### Response

``` http
HTTP/1.1 200 OK
Content-Type: application/spsp4+json

{
  "destination_account": "example.ilpdemo.red~invoice123",
  "shared_secret": "6jR5iNIVRvqeasJeCty6C+YB5X9FhSOUPCL/5nha5Vs=",
  "balance": "5360",
  "invoice": {
    "totalPaymentDue": {
      "price": 199.99,
      "priceCurrency": "USD"
    },
    "paymentDueDate": "2019-01-30T00:00Z",
    "paymentStatus": "http://schema.org/PaymentDue",
    "description": "Chair model 'Rustic'",
    "provider": "The Red Furniture Store",
    "asset": {
      "code": "USD",
      "scale": 2
  }
}
```

##### Response Body

The response body is a JSON object that includes basic account details necessary for setting up a STREAM connection (see [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md#Response-Body)) as well as optional parameters for displaying purposes. The optional parameters are defined in the following: 

| Field | Type | Description |
|---|---|---|
| `balance`  | String Integer | _(OPTIONAL)_ Amount, denoted in `invoice.asset.code`, which completes the invoice payment. |
| `invoice` | Object | _(OPTIONAL)_ Invoice details. It SHOULD follow the invoice schema proposed by [schema.org](https://schema.org/Invoice). Additionally, it SHOULD include the followin parameters:|
| `invoice.asset` | Object | _(OPTIONAL)_ Details about the Invoice's asset. |
| `invoice.asset.code` | String |  _(OPTIONAL)_ Asset code to identify the Invoice's currency. Currencies that have [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) codes should use those. |
| `invoice.asset.scale` | Integer |  _(OPTIONAL)_ The scale of the amounts denoted in `invoice.asset.code` (e.g. an amount of `"1000"` with a scale of `2` translates to `10.00` units of the SPSP server's asset/currency). |

**Note:** Currency amounts are denominated as integer strings instead of native JSON numbers to avoid losing precision during JSON parsing. Applications MUST represent these numbers in a data type that has precision equal or greater than an unsigned 64-bit integer.


##### Errors

###### receiver Does Not Exist

``` http
HTTP/1.1 404 Not Found
Content-Type: application/spsp4+json

{
  "id": "InvalidPointerError",
  "message": "Invoice does not exist."
}
```
