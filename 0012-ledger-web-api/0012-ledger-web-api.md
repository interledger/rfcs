# Ledger Web API

This spec defines some guidelines for **RESTful ledger APIs** to easily integrate with the Interledger Protocol suite.

The advantages of following this spec when designing a ledger are:
- A standardized interface for inter-ledger communication
- Easy adoption by connectors that implement the standard Web client (Example: `ilp-plugin-web`)

<p align="center">
  <img width="70%" height="70%" src ="./static/ilp_interface.png" />
</p>

## Requirements

In order for ledgers to integrate seamlessly with connectors the ledger needs to provide:
- a RESTful HTTP API with endpoints to initiate `transfers` and submit `fulfillments`
- PUSH notifications to notify connectors of changes in the ledger objects and incoming transfers or fulfillments. 
This could be through websockets, long-polling (EPOLL), or server-sent events.

TODO: define types (uuid, base58, base64, URI, ...)

## RESTful API Methods

### Authorization

TODO: explain how it works

### Ledger Metadata

#### Retrieve Metadata

Retrieve some metadata about the ledger. 

##### Request
```http
GET / HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    "precision": <int>,
    "scale": <int>,
    "currencyCode": <string: optional>,
    "currencySymbol": <string: optional>
}
```

For a detailed description of these properties, please see [`LedgerInfo`](https://github.com/interledger/rfcs/blob/master/0004-ledger-plugin-interface/0004-ledger-plugin-interface.md#class-ledgerinfo).

### Accounts

`TODO:` Account should be inline with the [ILP address specification](https://github.com/interledger/rfcs/blob/master/0004-ledger-plugin-interface/0004-ledger-plugin-interface.md#getaccount)

#### Retrieve account

##### Request
```http
GET /accounts/<uuid: ID> HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    "ledger": <uri>,
    "name": <string: optional>,
    "connector": <uri: optional>
}
```

`TODO:` define the fields
`TODO:` is the connector field required? Should the ledger be connector-agnostic?

#### Update account

##### Request
```http
PUT /accounts/<uuid: ID> HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    {
        "connector": <uri>,
        "name": <string: optional>
    }
```

`TODO:` define the fields
`TODO:` is the connector field required? Should the ledger be connector-agnostic?

##### Response
```http
HTTP/1.1 200 OK
{
    "ledger": <uri>,
    "name": <string>,
    "connector": <uri>
}
```

#### Retrieve account balance

Return a decimal string representing the current balance.

##### Request
```http
GET /accounts/<uuid: ID>/balance HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    "balance": <float>
}
```

### Transfers

Transfer payloads and responses need to conform to the [`Transfer` class](https://github.com/interledger/rfcs/blob/master/0004-ledger-plugin-interface/0004-ledger-plugin-interface.md#class-transfer).

#### Retrieve transfer item

##### Request
```http
GET /transfers/<uuid|base58: ID> HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
```

##### Response
```http
HTTP/1.1 200 OK
{
    "id": "<string: uuid|base58>",
    "amount": "<string: decimal value>",
    "debitAccount": "<string: ILP address>",
    "creditAccount": "<string: ILP address>",
    "data": "<JSON object>",
    "noteToSelf": "<JSON object>",
    "executionCondition": "<string: ILP condition URI>",
    "expiresAt": "<string: ISO 8601 timestamp>    
}
```

#### Create transfer item

##### Request
```http
POST /transfers/<uuid|base58: ID> HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    {
        "id": "<string: uuid|base58>",
        "amount": "<string: decimal value>",
        "debitAccount": "<string: ILP address>",
        "creditAccount": "<string: ILP address>",
        "data": "<JSON object>",
        "noteToSelf": "<JSON object>",
        "executionCondition": "<string: ILP condition URI>",
        "expiresAt": "<string: ISO 8601 timestamp>    
    }
```

##### Response
```http
HTTP/1.1 200 OK
```

#### Create/update fulfillment for transfer

##### Request
```http
PUT /transfers/<uuid|base58: ID>/fulfillment  HTTP/1.1
Host: ledger.example
Authorization: <token>/<cert>/<password>/...
Content-Type: application/json
Body:
    {
        "fulfillment" : "<string: ILP fulfillment URI>"
    }
```

##### Response
```http
HTTP/1.1 200 OK
```

## PUSH notifications (websockets)

The emitted events of the ledger should include the [LedgerPlugin events](https://github.com/interledger/rfcs/blob/master/0004-ledger-plugin-interface/0004-ledger-plugin-interface.md#events)

#### Open

```
uri: ws://ledger.example/<uuid: accountID>/transfers
```
