---
title: Plugin RPC API
draft: 1
---
# Plugin RPC API

## Description

> TODO

## Specification

### Send Transfer

#### Request

```http
POST /rpc/?method=send_transfer&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  {
    "id": "0e798bd6-213b-4b2f-bc1c-040788e7bae5",
    "amount": "348807",
    "ilp": "ARwAAAAAB1TUwA5nLnVzLm5leHVzLmJvYgMEEEEA",
    "executionCondition": "7td8LdXdYkv-6WXWdMlPZ1DhROwRFdazA0m3kTz4LUI",
    "expiresAt": "2017-06-14T11:58:18.509Z"
  }
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

true
```

### Send Request (ILQP)

#### Request

```http
POST /rpc/?method=send_request&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  {
    "ilp": "ARwAAAAAB1TUwA5nLnVzLm5leHVzLmJvYgMEEEEA"
  }
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "ilp": "AEEEEMgYvJmLzVHel5mLzVnLn5AwUT1BAAAAAwRA"
}
```

### Send Request (Routing)

#### Request

```http
POST /rpc/?method=send_request&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  {
    "custom": {
      "method": "broadcast_routes",
      "data": {
        "new_routes": [ {
          "source_ledger": "peer.me.",
          "destination_ledger": "g.ledger.",
          "points": "AAAAAAAAAAAAAAAAAAAAAP////////////////////8=",
          "min_message_window": 1,
          "paths": [ [] ],
          "source_account": "peer.me.P74ZwUNQr3QFK7UjCU4Is9ZuWUHtMqIuA"
        } ],
        hold_down_time: 600000,
        unreachable_through_me: []
      }
    }
  }
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "custom": {}
}
```

### Fulfill Condition

#### Request

```http
POST /rpc/?method=fulfill_condition&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  "0e798bd6-213b-4b2f-bc1c-040788e7bae5",
  "yMy5Sy5dTjQASrNjS0SywjbwH9nQaiFMWJv1QD3Q_VE"
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

true
```

### Reject Incoming Transfer

#### Request

```http
POST /rpc/?method=reject_incoming_transfer&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  "0e798bd6-213b-4b2f-bc1c-040788e7bae5"
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

true
```

### Get Limit

#### Request

```http
POST /rpc/?method=get_limit&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

"-5000000000"
```

### Get Balance

#### Request

```http
POST /rpc/?method=get_balance&prefix=peer.me HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

"10230045000"
```
