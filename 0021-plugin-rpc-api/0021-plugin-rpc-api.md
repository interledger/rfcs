---
title: Plugin RPC API
draft: 3
---
# Plugin RPC API

This spec depends on the [LPI spec](../0004-ledger-plugin-interface/).

## Description

This specification details how to serialize Interledger's Ledger Plugin Interface over http.

## Specification

For every method of the LedgerPlugin class, it defines a Remote Procedure Call (RPC) method.
All RPC methods are implemented as a http or
https POST to an endpoint URL, with the method name as the 'method' query parameter.
The post body is a JSON document representing the array of method arguments.

For each `incoming_*` event defined by the LPI spec, a corresponding RPC call will be made in the opposite direction,
namely:
* `incoming_transfer` -> `sendTransfer`
* `incoming_fulfill` -> `fulfillCondition`
* `incoming_reject` -> `rejectIncomingTransfer`
* `incoming_request` -> `sendRequest`

Note incoming requests are a special case, because they require a response.
Instead of taking the request response from the currently registered request handler, a http call for the `sendRequest`
method is made, and its response body parsed as a JSON document.

Calls to `connect` and `disconnect`, `registerRequestHandler` and `deregisterRequestHandler`
are silently ignored, and `isConnected` alwqys returns true.

## Example (Send Transfer)

#### Request

```http
POST /rpc/?method=sendTransfer HTTP/1.1
Host: rpchost
Accept: application/json
Content-Type: application/json
Authorization: Bearer ABCXYZ

[
  {
    "id": "0e798bd6-213b-4b2f-bc1c-040788e7bae5",
    "from": "peer.me.P74ZwUNQr3QFK7UjCU4Is9ZuWUHtMqIuA",
    "to": "peer.me.Y_luxphkAy6ddYzuXb9lXxS60zg5tHjrPh8zz_BfwEA",
    "ledger": "peer.me.",
    "amount": "348807",
    "ilp": "ARwAAAAAB1TUwA5nLnVzLm5leHVzLmJvYgMEEEEA",
    "noteToSelf": {},
    "executionCondition": "7td8LdXdYkv-6WXWdMlPZ1DhROwRFdazA0m3kTz4LUI",
    "expiresAt": "2017-06-14T11:58:18.509Z",
    "custom": "outgoing"
  }
]
```

#### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json

true
```
