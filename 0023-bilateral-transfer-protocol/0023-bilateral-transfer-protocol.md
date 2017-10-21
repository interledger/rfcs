---
title: Bilateral Transfer Protocol (BTP)
draft: 2
---
# Bilateral Transfer Protocol (BTP)

## Preface

This document describes the Bilateral Transfer Protocol (BTP), a ledger
protocol for bilateral transfers of value. It the successor to [Plugin
RPC](https://github.com/interledger/rfcs/blob/master/0021-plugin-rpc-api/0021-plugin-rpc-api.md#plugin-rpc-api),
and has been written to use OER instead of JSON.

## Introduction

### Motivation

There are many different types of ledgers, and Interledger aims to interoperate
all of them. For fast ledgers that support hash time locks, memos, and
messaging, it is enough to wrap the ledger's API in a [Ledger
Plugin](https://github.com/interledger/rfcs/blob/master/0004-ledger-plugin-interface/0004-ledger-plugin-interface.md).
These allow you to send interledger payments through anyone else on that ledger
who is running your plugin.

In lots of scenarios, we don't have an underlying ledger that's fast enough to
do every ILP payment on-ledger. If two parties want to transact, they can send
transfers directly to one another with BTP. BTP requires that the two parties
trust one another (up to a limit) for funds that have not yet been settled on
the underlying ledger. If their trust limit is high enough, the two parties can
transact without settling on an underlying ledger at all.

Because we believe the use case for a bilateral ledger protocols is so
ubiquitous, the BTP has been designed to be efficient to transmit and friendly
to re-implement.

### Scope

BTP manages conditional transfers, messaging requests, result/error reporting,
and carries sub-protocols (sometimes called side-protocols) for extensibility.
You can use ILP without using BTP. BTP is not a ledger in itself, but it is a
ledger-layer protocol in the [ILP
architecture](https://github.com/interledger/rfcs/blob/master/0001-interledger-architecture/0001-interledger-architecture.md)
because it handles local transfers.

BTP is intended to be a well-suited solution so that a new bilateral ledger
protocol doesn't need to exist for every new use case. It also includes
functionality which is common between many different ledger types, making it a
good place to start from when creating a new bilateral protocol for transfering
value.

This document describes the flow and data format that BTP uses, but not
sub-protocols. Sub-protocols include optional functionality like ledger
metadata, balance, automated settlement, and dispute resolution. Some protocols
are documented on [the wiki
page](https://github.com/interledger/interledger/wiki/Interledger-over-CLP).
They are carried in the protocol data of BTP packets.

The BTP packet format is described exactly in the [BTP ASN.1
spec](https://github.com/interledger/rfcs/blob/master/asn1/BilateralTransferProtocol.asn).

## Terminology

- **BTP** is the bilateral transfer protocol, as described by this document and the
  ASN.1 spec.

- A **Sub-Protocol** is a protocol which isn't defined by BTP and is carried
  in the protocol data (see below). The first one is the primary sub-protocol,
  subsequent entries are secondary sub-protocols.

- A **BTP Connection** is a websocket connection over which BTP packets are
  sent. Websockets (as opposed to raw TLS sockets) are used because they provide
  message framing and can be used from the browser.

- **BTP Packets** are the protocol data units described in this document. They are
  formally defined in the [BTP ASN.1 spec](https://github.com/interledger/rfcs/blob/master/asn1/BilateralTransferProtocol.asn).

- **Peers** are the parties on a BTP connection. Your peer is the party on the
  other side of the BTP connection.

- The **Bilateral Ledger** is the ledger which the peers on a BTP connection
  are keeping track of. When a peer keeping Authoritative State receives a BTP
packet, they process it and adjust their copy of the bilateral ledger. The
bilateral ledger is not to be confused with the Underlying Ledger.

- **Authoritative State** is the authoritative view of the Bilateral Ledger's
  state, maintained by one or both of the peers. Because both peers on a BTP
connection can keep authoritative state, they can get into dispute if they
disagree on the state of a transfer. This usually happens when network latency
causes the peers to disagree about expiries. If one party keeps authoritative
state, the other party must trust them not to tamper with it.

- A request is **In-Flight** if the request has been sent out, but no response
  has been sent yet. A transfer is **In-Flight** if it has been prepared but
not yet fulfilled nor rejected.

- An **Underlying Ledger** moves value between the two peers when they settle
  their balance. If Peer 1 owes Peer 2 100 XRP, Peer 1 could send Peer 2 100
XRP on Ripple in order to make their balance 0. In that scenario, XRP ledger is
the underlying ledger.

## Overview

BTP is broken up into 4 different RPC requests, which can get 2 different
responses. Every BTP packet follows a common structure:

```
  +---------------+
1 | Type (1)      |
  +---------------+
1 | Request ID    |
2 | (2)           |
3 |               |
4 |               |
  +---------------+
1 | Length Prefix |
2 | (3)           |
  +---------------+
  | Packet-       |
  | Specific      |
  | Data          |
  . (4)           |
  .               |
  .               |
  |               |
  +---------------+
1 | Sub-Protocol  |
2 | Count (5)     |
  +---------------+
  | Sub-Protocol  |
  | Data          |
  . (6)           |
  .               |
  .               |
  |               |
  +---------------+
```

1. **Type**: A 1-byte value describing what type of BTP packet this is.
The values are described below, in [BTP Type IDs](#btp-type-ids).

2. **Request ID**: A random 4-byte value used to correlate requests 
and responses. This value MAY be sequential instead of random, but care must
be taken so that duplicate IDs are never in-flight at the same time.

3. **Length Prefix**: A 1-byte (if under 128) or 2-byte value, containing the
combined length of the packet-specific data and protocol data sections.

4. **Packet-Specific Data:** Fields specific to the type of BTP packet. Variable
length.

5. **Sub-Protocol Count:** Variable-length integer containing the number of
sub-protocols carried by this packet.

5. **Sub-Protocol Data:** A list of protocols, containing a string (the protocol's name), a 1-byte flag (containing the MIME type), and a length-prefixed octet string (containing the protocol's data). Exact description is below in [Sub-Protocol Data Format](#sub-protocol-data-format).

### BTP Type IDs

| ID | Type | Request/Response |
|:--|:--|:--|
| 1 | `Response` | Response |
| 2 | `Error` | Response |
| 3 | `Prepare` | Request |
| 4 | `Fulfill` | Request |
| 5 | `Reject` | Request |
| 6 | `Message` | Request |

### Sub-Protocol Data Format

```asn1
ContentType ::= INTEGER {
  applicationOctetString  (0),
  textPlainUtf8           (1),
  applicationJson         (2)
} (0..255)

ProtocolData ::= SEQUENCE OF SEQUENCE {
  protocolName IA5String,
  contentType ContentType,
  data OCTET STRING
}
```

## Authentication

Before anything else, when a client connects to a server, it sends a special
`Message` request. Its primary `protocolData` entry MUST have name `'auth'`,
content type `MIME_APPLICATION_OCTET_STREAM`,
and empty data, and among the secondary entries, there MUST be a UTF-8
`'auth_token'` entry, and a UTF-8 `'auth_username'` entry. The further secondary
protocol data entries of this `Message` request MAY also be used to send
additional information to the server. In situations where no authentication
is needed, the `'auth_token'` and `'auth_username'` data can be set to the
empty string, but they cannot be omitted.

If the client sends any BTP call that is not a Message, or sends a Message call
whose primary sub-protocol is not `auth`, the server should respond with an `Error`
and close the connection.

The server responds with a `Response` or `Error` as appropriate. Again, the
`protocolData` field there MAY be used to send additional information to
the client. To be clear, the server responds with an `Error` if:

* any other packet is sent before the auth data
* the provided authentication data is invalid or incorrect
* any of the other protocol rules are violated (e.g. having two subprotos with the same name)
* it takes too long before the authentication data is sent.

If the server sent an `Error`, it subsequently closes the connection.
If the server sent a `Response`, the BTP connection is open, until either
one of the parties closes it. At the BTP level, the client and server play
identical roles.

If the client does not send an Auth packet within a reasonable time, the
server optionally sends a Message informing the client that the authentication timed out,
and then closes the connection. If the client did send an Auth packet, but
got neither a `Response` nor an `Error` back from the server, the client
closes the connection.

If the connection is ever dropped and reconnected then it must be re-authenticated.

## Sub-protocols

In order to understand the different BTP calls, it is necessary to distinguish between the first ("primary") and subsequent ("secondary") sub-protocol entries. The primary sub-protocol
entry defines what type of action or information is requested of the recipient of the message. The secondary sub-protocols should not request additional actions or information. If multiple actions or
pieces of information are required, multiple separate Messages should be sent. The secondary sub-protocols should only modify the request made in the primary sub-protocol, or provide additional contextual data which can be consumed in a readonly way (without affecting the result).

For example, the primary sub-protocol entry of a Message might represent a quote request, while one additional secondary sub-protocol entry may be present, indicating this request was forwarded by a proxy.

Likewise, only the primary sub-protocol data in a Response indicates whether result of the request from the Message being responded to actually succeeded or not.

In Error, Prepare, Fulfill, and Reject calls, the distinction between primary and secondary sub-protocol entries is less strict.

## Flow

BTP uses a simple RPC flow. A request-type BTP packet is sent, and a
response-type BTP packet is sent in response with the same request ID. The
request types are `Message`, `Prepare`, `Fulfill` and `Reject`, and the
response types are `Response` and [`Error`](#error).

Because it would be too slow to atomically save all requestIds that are
processed, they are not idempotent. It is the responsibility of the requestor
to make sure they don't duplicate requestIds. The implementation should ensure
that no two in-flight requests are sent out with the same requestId. The
responder should always send back a response to a request with the same
requestId.

There are also a couple of tricky cases to handle:

- If an unexpected BTP packet is received, no response should be sent. An unexpected BTP packet is a response for which a request was not sent, or a response for a request which has already been responded to.
- If an unreadable BTP packet is received, no response should be sent. An unreadable BTP packet is one which is structurally invalid, i.e. terminates before length prefixes dictate or contains illegal characters.

These behaviors are important for preventing accidental feedback loops.  If an
unexpected packet triggered an error, that error may be unexpected to the
sender. The sender would reply with another unexpected error, causing an
infinite loop. Unreadable packets must be ignored too. If an application got
onto a BTP connection and spoke the wrong protocol, it would trigger an error
from BTP. This might trigger an error from the application, and it would
devolve into another infinite loop.

### Message

```asn1
Message ::= SEQUENCE {
  protocolData ProtocolData
}
```

`Message` is used for sending information to the peer. It contains no
packet-specific data, only protocol data. [ILQP](https://github.com/interledger/rfcs/blob/master/0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md) packets are attached under the
protocol name `ilp` with content-type `application/octet-stream`.

- `Response` is returned if the peer acknowledges the `Message`. If the peer
  has data to send in reply (e.g. a quote response), it is carried in the
protocol data.

- `Error` is returned if the peer is not able to process the `Message`, or there
  was an unexpected error and further `Message`s should not be sent. This does
not include ILP errors such as "No quote found", only the cases in which the
`Message` cannot be sent/processed at all.

### Prepare

```asn1
Prepare ::= SEQUENCE {
  transferId UInt128,
  amount UInt64,
  executionCondition UInt256,
  expiresAt Timestamp,
  --
  protocolData ProtocolData
}
```

`Prepare` is used to create a transfer on the bilateral ledger. The packet
data contains `transferId`, `amount`, `executionCondition`, and `expiresAt`.
`Prepare` is a request with side effects, because it creates a transfer with
the given details. This transfer begins in the `prepared` state.

`transferId` is a securely random 128-bit unique ID that references the
transfer.  `amount` is a 64-bit integer denominated in ledger base units. The
ledger base units can be anything, so long as both parties on the bilateral
ledger agree on their meaning. Examples of base units are "micro-XRP,"
"satoshi," or "nano-dollars settled over paypal." `executionCondition` is a
256-bit integer containing the SHA-256 hash of this conditional transfer's
fulfillment.  `expiresAt` is a ASN.1 UTC GeneralizedTime containing the expiry
of this transfer. The GeneralizedTime MUST be in UTC (i.e. no timezone info).

ILP payment packets are attached to the protocol data under the protocol
name `ilp` and the MIME type `application/octet-stream`. 

- `Response` is returned if the peer acknowledges the `Prepare`. This means the
  transfer is now `prepared` and has been applied to the balance. It may carry
sub-protocol data, for example a payment channel claim.

- `Error` is returned if the peer does not accept the transfer. This could be
  because it is incompatible with an existing transfer with the same ID (see
Idempotency below), or because it exceeds some constraint your peer has placed.
The amount could be too high, or could exceeds the balance. If the transfer ever enters the `prepared` state, an `Error` should not be returned. Instead, a `Reject` call should be made.

#### Idempotency

If a transfer with the given ID already exists in any state, a new transfer
should not be created. If the packet (including protocol data) matches an
existing transfer exactly and that transfer is in the `prepared` state, a
`Response` should be returned. If the packet (including protocol data) shares
the ID of an existing transfer but other details do not match, an `Error`
should be returned. If the packet (including protocol data) exactly
matches an existing transfer but that transfer is in the `fulfilled` state or
the `rejected` state, an `Error` should be returned.

#### Expiry

After the `expiresAt` date is reached, the transfer can no longer be fulfilled.
If one party on the BTP connection is keeping authoritative state, they MUST
send a `Reject` request to the other party. If both parties are keeping
authoritative state, they MAY independently expire the transfer (set the state
to `rejected` and roll it back) automatically.

### Fulfill

```asn1
Fulfill ::= SEQUENCE {
  transferId UInt128,
  fulfillment UInt256,
  --
  protocolData ProtocolData
}
```

`Fulfill` is used to change an existing transfer from the `prepared` state to
the `fulfilled` state. The packet-specific data of `Fulfill` is made up of `transferId`
and `fulfillment`. `Fulfill` is a request with side effects: it changes the
state of the transfer and finalizes the transfer's balance update. If the
transfer is already fulfilled, no changes are applied.

`transferId` is a 128-bit unique ID, which references an existing transfer.
`fulfillment` is a 256-bit integer, containing the preimage of the
`executionCondition` of the referenced transfer.

A `Fulfill` request must be sent from the receiver of the referenced transfer,
not the sender.

A `Fulfill` request is successful if `transferId` references an existing
transfer in the `prepared` state, the `fulfillment` is the SHA-256 preimage of
the referenced transfer's `executionCondition`, and the current time (when the
request is being processed) is before the referenced transfer's `expiresAt`.

A `Fulfill` request is also successful if the transfer is in the `fulfilled`
state, and this packet matches the one that fulfilled the transfer,
including protocols but not including requestId.

- `Response` is returned if the request is successful.  This means the
  transfer's state is now `fulfilled`, and its balance change has been
finalized.

- `Error` is returned if there is no transfer with the given ID, the
  fulfillment does not match the condition, the expiresAt has already passed,
or the transfer has been `rejected`.

### Reject

```
Reject ::= SEQUENCE {
  transferId UInt128,
  --
  protocolData ProtocolData
}
```

`Reject` is used to change an existing transfer from the `prepared`
state to the `rejected` state. The packet-specific data of `Reject` is made up
only of `transferId`.

`transferId` is a 128-bit unique ID, which references an existing transfer.
The reason that the transfer was rejected should go in the protocol data.  For
example, if this is an ILP Payment being rejected, the `ilp` protocol will
contain an [ILP
Error](https://github.com/interledger/rfcs/blob/master/0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-format).

A `Reject` request must come from the receiver of the referenced transfer,
not the sender.

A `Reject` request is successful if `transferId` references an existing
transfer in the `prepared` state.

A `Reject` request is also successful if `transferId` references an existing
transfer in the `rejected` state, and this packet matches the one that
rejected this transfer, including protocols but not including requestId.

- A `Response` is returned if the request is successful. This indicates that
  the balance changes of the referenced transfer have been rolled back.

- An `Error` is returned if the request was not successful.

### Error

```
Error ::= SEQUENCE {
  -- Standardized error code
  code IA5String (SIZE (3)),
  -- Corresponding error code
  name IA5String,
  -- Time of emission
  triggeredAt Timestamp,
  -- Additional data
  data OCTET STRING (SIZE (0..8192)),
  --
  protocolData ProtocolData
}
```

`Error` is a response-type message, returned when an error occurs on the BTP
level. It has packet-specific data which resembles the [ILP Error
format](https://github.com/interledger/rfcs/blob/master/0003-interledger-protocol/0003-interledger-protocol.md#ilp-error-format),
but irrelevant fields have been taken off and new error codes have been
written:

#### Error Codes

Errors marked with a `T` are temporary, and can be retried after a short
(1-60s) wait. If a retry fails again with a temporary error, a BTP client
SHOULD wait longer before trying again. Errors marked with `F` are final, and
the same request MUST NOT be retried.

| Code | Name | Description |
|:--|:--|:--|
| **T00** | UnreachableError | Temporary error, indicating that the connector cannot process this request at the moment. Try again later. |
| **F00** | NotAcceptedError | Data were symantically invalid. |
| **F01** | InvalidFieldsError | At least one field contained structurally invalid data, e.g. timestamp full of garbage characters. |
| **F03** | TransferNotFoundError | The transferId included in the packet does not reference an existing transfer. |
| **F04** | InvalidFulfillmentError | The fulfillment included in the packet does not match the transfer's condition. |
| **F05** | DuplicateIdError | The transferId and method match a previous request, but other data do not. |
| **F06** | AlreadyRolledBackError | The transfer cannot be fulfilled because it has already been rejected or expired. |
| **F07** | AlreadyFulfilledError | The transfer cannot be rejected because it has already been fulfilled. |
| **F08** | InsufficientBalanceError | The transfer cannot be prepared because there is not enough available liquidity. |
