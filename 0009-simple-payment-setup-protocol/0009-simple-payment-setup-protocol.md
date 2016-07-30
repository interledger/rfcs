# Simple Payment Setup Protocol (SPSP)

The Simple Payment Setup Protocol (SPSP) is a basic application-layer Interledger protocol for wallet-to-wallet or wallet-to-merchant payments.

## Stages

SPSP performs its function in five stages:

1. Discovery
2. Query
3. Quoting
4. Setup
5. Execution

### Discovery

Whenever possible, URIs should be exchanged out-of-band and discovery should be skipped. However, in some cases, it may be useful to have a standardized user-friendly identifier. This discovery method describes how to resolve such an identifier to a queryable SPSP endpoint.

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

### Query

Any SPSP recipient will create a receiving endpoint called the *receiver*. The sender queries this endpoint to get information about the type of payment that can be made to this receiver:

``` http
GET /api/receivers/bob HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json
```
``` http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "type": "payee",
  "ledger": "https://red.ilpdemo.org/ledger",
  "account": "https://red.ilpdemo.org/ledger/accounts/bob",
  "payments": "https://red.ilpdemo.org/api/receiver/bob/payments"
}
```

[Try this request](https://red.ilpdemo.org/api/receivers/bob)

Possible values for `type` are:

`payee`
: This is a general receiving account for peer-to-peer payments.

`invoice`
: This is an invoice, meaning it can be paid only once and only with a specific amount.

#### Payee

Payee information consists of basic account details. Amounts are chosen by the sender.

**Example Receiver**
``` json
{
  "type": "payee",
  "ledger": "https://red.ilpdemo.org/ledger",
  "account": "https://red.ilpdemo.org/ledger/accounts/bob",
  "payments": "https://red.ilpdemo.org/api/receiver/bob/payments"
}
```

If this receiver is not available, an error can be generated at this stage:

``` http
HTTP/1.1 404 Not Found
Content-Type: application/json

{
  "id": "InvalidReceiverIdError",
  "message": "Invalid receiver ID"
}
```

#### Invoice

Invoice information includes an exact amount as well as the status of the invoice. (Invoices can only be paid once.)

**Example Receiver**
``` json
{
  "type": "invoice",
  "ledger": "https://red.ilpdemo.org/ledger",
  "account": "https://red.ilpdemo.org/ledger/accounts/amazon",
  "amount": "10.40",
  "status": "unpaid",
  "invoice_info": "https://www.amazon.com/gp/your-account/order-details?ie=UTF8&orderID=111-7777777-1111111",
  "payments": "https://red.ilpdemo.org/api/invoice_receiver/amazon/111-7777777-1111111/payments"
}
```

### Quoting

The sender requests quotes from neighboring connectors using [ILQP](../0008-interledger-quoting-protocol/).

### Setup

When the sender is ready to make a payment, it submits a payment object to the receiver:

``` http
POST /api/receiver/bob/payments HTTP/1.1
Host: red.ilpdemo.org
Accept: application/json

{
  "amount": "10.40",
  "source_identifier": "alice@blue.ilpdemo.org",
  "memo": "Hey Bob!"
}
```
``` http
HTTP/1.1 201 Created
Content-Type: application/json

{
  "receipt_condition": "cc:1:1:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:1"
}
```

The setup is what primes the receiver to expect the incoming payment. It also provides the sender with the correct execution condition which describes the signed receipt which the receiver will generate to provide proof-of-payment.

The receiver has the opportunity to reject an incoming payment before any funds move, for instance because of daily limits:

``` http
HTTP/1.1 422 Unprocessable Entity
Content-Type: application/json

{
  "id": "LimitExceededError",
  "error": "Daily incoming funds limit exceeded"
}
```

### Execution

The sender initiates a transfer on their local ledger using the [Interledger Protocol](../0003-interledger-protocol/).
