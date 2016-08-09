# Simple Payment Setup Protocol (SPSP)

The Simple Payment Setup Protocol (SPSP) is a basic application-layer Interledger protocol for wallet-to-wallet or wallet-to-merchant payments. It uses HTTPS for communication between the sender and recipient of an ILP payment.

## The Receiver Endpoint

Any SPSP recipient will create a receiving HTTP endpoint called the *receiver*. The sender can Query this endpoint to get information about the type of payment that can be made to this receiver. The sender also uses the receiver endpoint to Setup the ILP payment.

### Query (`GET <receiver>`)

The sender queries the receiver endpoint to get information about the type of payment that can be made to this receiver:

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
  "account": "ilpdemo.red.bob"
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
  "account": "ilpdemo.red.bob"
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
  "account": "ilpdemo.red.amazon.111-7777777-1111111",
  "amount": "10.40",
  "status": "unpaid",
  "invoice_info": "https://www.amazon.com/gp/your-account/order-details?ie=UTF8&orderID=111-7777777-1111111"
}
```

### Setup (`POST <receiver>`)

When the sender is ready to make a payment, it submits a payment object to the receiver.

``` http
POST /api/receiver/bob HTTP/1.1
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
  "packet": "asdglkjlsdfoiuaosiduf...",
  "condition": "cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0"
}
```

The setup is what primes the receiver to expect the incoming payment. The receiver generates the ILP packet the sender will need to use to send this payment and uses the [Interactive Transport Protocol](../0011-interactive-transport-protocol) to generate the execution condition. The fulfillment of the condition will serve as the sender's proof of payment.

The receiver has the opportunity to reject an incoming payment before any funds move, for instance because of daily limits:

``` http
HTTP/1.1 422 Unprocessable Entity
Content-Type: application/json

{
  "id": "LimitExceededError",
  "error": "Daily incoming funds limit exceeded"
}
```

## Appendix

### Appendix A: (Optional) Webfinger Discovery

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

