---
draft: 1
title: ILP Over HTTP
---
# ILP Over HTTP

This spec defines a minimal [Ledger Layer](./0001-interledger-architecture/0001-interledger-architecture.md#ledger-layer) protocol using the Hyper Text Transfer Protocol (HTTP). It includes the Interledger payment fields (such as destination address) alongside those that are local to a specific hop (such as the transfer amount).

**Note:** This protocol is not to be confused with [HTTP ILP](./0014-http-ilp/0014-http-ilp.md), which defines HTTP headers for communicating payment details on a normal HTTP request to an application server. The values defined in this protocol will be forwarded to the destination ILP address defined in the request.

## Overview

It's everything you need to do ILP with just a couple of HTTP headers on a POST request/response. What more do we need to say?

## Specification

This protocol SHOULD be used with HTTPS or HTTP/2. It SHOULD NOT be used with insecure HTTP except for testing purposes.

### Request

```http
POST / HTTP/1.1
ILP-Destination: g.crypto.bitcoin.1XPTgDRhN8RFnzniWCddobD9iKZatrvH4.~asdf1234
ILP-Condition: x73kz0AGyqYqhw/c5LqMhSgpcOLF3rBS8GdR52hLpB8=
ILP-Expiry: 2017-12-07T18:47:59.015Z
ILP-Amount: 1000

<body>
```

| Field | Type | Modified at Each Hop? | Description |
|---|---|---|---|
| `ILP-Destination` | [ILP Address](./0015-ilp-addresses/0015-ilp-addresses.md) | N | Destination address of the payment |
| `ILP-Condition` | Base64-Encoded String, 32 Bytes | N | Execution condition of the payment, which is the Sha256 hash digest of the condition fulfillment |
| `ILP-Expiry` | [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) Timestamp in UTC | Y | Expiry of the transfer |
| `ILP-Amount` | Unsigned 64-Bit Integer | Y | Transfer amount, denominated in the minimum divisible units of the ledger. Note that this is the local transfer amount, **not** the destination amount as in the original [ILP Payment Packet Format](https://github.com/interledger/rfcs/blob/master/0003-interledger-protocol/0003-interledger-protocol.md#ilp-payment-packet-format) |
| `<body>` | Binary, Maximum of 32767 Bytes | N | End-to-end data used by Transport Layer protocols |
| `ILP-...` | UTF-8 String | N | Additional headers that MUST be forwarded by all connectors, even if they are not understood |
| `ILP-Destination-Amount` | Unsigned 64-Bit Integer | N | _(OPTIONAL)_ The amount the connectors should attempt to deliver to the destination account. If unspecified, connectors will forward the payment to the destination by applying their local rate. Not all connectors will support delivery so Transport Layer protocols that set this field SHOULD accept overpayment. |

### Response

#### Success

```http
HTTP/1.1 200 OK
ILP-Fulfillment: cz/9RGv1PVjhKIOoyPvWkAs8KrBpIJh8UrYsQ8j34CQ=

<body>
```

| Field | Type | Modified at Each Hop? | Description |
|---|---|---|---|
| `ILP-Fulfillment` | Base64-Encoded String, 32 Bytes | N | Preimage of the `ILP-Condition` |
| `<body>` | Binary, Maximum of 32767 Bytes | N | End-to-end data used by Transport Layer protocols |
| `ILP-...` | UTF-8 String | N | Additional headers that MUST be forwarded by all connectors, even if they are not understood |

#### Error

HTTP Error Codes MAY be used to indicate certain types of failures, but [ILP Error Codes](./0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-codes) MUST be used and relayed by connectors.

```http
HTTP/1.1 404 Not Found
ILP-Error-Code: F02
ILP-Error-Name: Unreachable
ILP-Error-Triggered-By: g.usd.acmebank.user12345.xclkv-909sdf
ILP-Error-Triggered-At: 2017-12-07T19:11:21.917Z
ILP-Error-Forwarded-By: g.usd.acmebank.connector,g.crypto.bitcoin.1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa

<body>
```

| Field | Type | Modified at Each Hop? | Description |
|---|---|---|---|
| `ILP-Error-Code` | [ILP Error Code](./0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-codes) | N | 3-letter code identifying the error |
| `ILP-Error-Name` | String | N | Human-readable name corresponding to the `ILP-Error-Code` |
| `ILP-Error-Triggered-By` | ILP Address | N | Address of the party that initially emitted the error |
| `ILP-Error-Triggered-At` | ISO 8601 Timestamp in UTC | N | Time when the error was initially emitted |
| `ILP-Error-Forwarded-By` | Comma-Separated List of ILP Addresses | Y | List of connectors that relayed this error. Connectors SHOULD append their ILP addresses to the end of this list when relaying the error |
| `<body>` | Binary, Maximum of 32767 Bytes | N | End-to-end data used by Transport Layer Protocols |
| `ILP-...` | UTF-8 String | N | Additional headers that MUST be forwarded by all connectors, even if they are not understood |
