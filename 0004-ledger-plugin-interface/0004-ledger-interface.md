# Ledger Interface

This spec defines some guidelines for **RESTful ledger APIs** to easily integrate with the Interledger Protocol suite.

The advantages of following this spec when designing a ledger are:
- A standardized interface for inter-ledger communication
- Easy adoption of existing interledger plugins

## Requirements

In order for ledgers to connect seamlessly with any of the ILP plugins `ilp-plugin-<ledgerID>`, the ledger needs to provide:
- a RESTful HTTP API with endpoints to `transfer` (or `transaction`, `asset`) objects
- PUSH notifications to register changes in the ledger objects, albeit using websockets, long-polling (EPOLL), or server-sent events.

## RESTful API Methods

### Ledger Metadata

#### Retrieve Metadata

##### Request
```http
GET / HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    'precision': <int>,
    'scale': <int>,
    'currencyCode': <string: optional>,
    'currencySymbol': <string: optional>
}
```

### Accounts

#### Retrieve account

##### Request
```http
GET /accounts/<ID> HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    'ledger': <uri>,
    'name': <string: optional>,
    'connector': <uri: optional>
}
```

#### Update account

##### Request
```http
PUT /accounts/<ID> HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    {
        'connector': <uri>,
        'name': <string: optional>
    }
```

##### Response
```http
HTTP/1.1 200 OK
{
    'ledger': <uri>,
    'name': <string>,
    'connector': <uri>
}
```

#### Retrieve account balance

##### Request
```http
GET /accounts/<ID>/balance HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    'balance': <float>
}
```

#### Retrieve connectors

##### Request
```http
GET /connectors/ HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
[
    {
        'connector': <uri>
    },
    ...
]
```


### Transfers

#### Retrieve transfer item

##### Request
```http
GET /transfers/<ID> HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
ledgerTransfer
```

#### Create transfer item

##### Request
```http
POST /transfers/<ID> HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    ledgerTransfer
```

##### Response
```http
HTTP/1.1 200 OK
ledgerTransfer
```

#### Retrieve fulfillment for transfer

##### Request
```http
GET /transfers/<ID>/fulfillment HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
ilpFulfillment
```

#### Create/update fulfillment for transfer

##### Request
```http
PUT /transfers/<ID>/fulfillment  HTTP/1.1
Host: ledger.my
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    ilpFulfillment
```

##### Response
```http
HTTP/1.1 200 OK
ilpFulfillment
```

## PUSH notifications (websockets)

#### Open

```
uri: ws://ledger.my/<accountID>/transfers
```
