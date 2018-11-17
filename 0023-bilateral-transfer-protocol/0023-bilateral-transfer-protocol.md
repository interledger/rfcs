---
title: Bilateral Transfer Protocol 2.0 (BTP/2.0)
draft: 8
---
# Bilateral Transfer Protocol 2.0 (BTP/2.0)

## Preface

This document describes version 2.0 of the Bilateral Transfer Protocol (BTP), a request/response
protocol for bilateral WebSocket links between Interledger connectors.

## Introduction

### Motivation

When two Interledger connectors send ILPv4 packets over HTTP POST,
they each need to act as an HTTP server at times. If one of the connectors runs behind a firewall,
this may be impossible. Therefore, BTP uses WebSockets instead of HTTP. With
WebSockets, only one of the connectors needs to be publicly addressable.

However, WebSockets don't provide a mechanism for relating responses to requests. BTP adds this missing
request/response layer, between WebSockets and the request/response pairs exchanged by the connectors.

### Scope

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
  has been received yet.

## Overview

BTP is broken up into one different RPC requests, which can get two different
responses. The following is a common BTP packet structure, though some types
don't have `Packet Specific Data` section:

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
length. Some types don't have this section. See [ASN.1 definitions](../asn1/BilateralTransferProtocol.asn) for details.

5. **Sub-Protocol Count:** Variable-length integer containing the number of
sub-protocols carried by this packet.

5. **Sub-Protocol Data:** A list of protocols, containing a string (the protocol's name), a 1-byte flag (containing the MIME type), and a length-prefixed octet string (containing the protocol's data). Exact description is below in [Sub-Protocol Data Format](#sub-protocol-data-format).

### BTP Type IDs

| ID | Type | Request/Response |
|:--|:--|:--|
| 1 | `Response` | Response |
| 2 | `Error` | Response |
| 3 | (not used) |  |
| 4 | (not used) |  |
| 5 | (not used) |  |
| 6 | `Message` | Request |
| 7 | `Transfer` | Request |

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
`'auth_token'` entry. The further secondary
protocol data entries of this `Message` request MAY also be used to send
additional information to the server. In situations where no authentication
is needed, the `'auth_token'` data can be set to the
empty string, but it cannot be omitted.

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

In Error calls, the distinction between primary and secondary sub-protocol entries is less strict.

## Flow

BTP uses a simple RPC flow. A request-type BTP packet is sent, and a
response-type BTP packet is sent in response with the same request ID. The
request types are `Message` and `Transfer`, and the
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
packet-specific data, only protocol data. [ILP](https://github.com/interledger/rfcs/blob/master/0003-interledger-protocol/0003-interledger-protocol.md#ilp-payment-packet-format) packets are attached under the
protocol name `ilp` with content-type `application/octet-stream`.

- `Response` is returned if the peer acknowledges the `Message`. If the peer
  has data to send in reply (e.g. a quote response), it is carried in the
protocol data.

- `Error` is returned if the peer is not able to process the `Message`, or there
  was an unexpected error and further `Message`s should not be sent. This does
not include ILP errors such as "No quote found", only the cases in which the
`Message` cannot be sent/processed at all.

### Error

```
Error ::= SEQUENCE {
  -- Standardized error code
  code IA5String (SIZE (3)),
  -- Corresponding error code
  name IA5String,
  -- Time of emission
  triggeredAt GeneralizedTime,
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

### Transfer

```asn1
Transfer ::= SEQUENCE {
  amount UInt64,
  --
  protocolData ProtocolData
}
```

`Transfer` is used to send proof of payment, payment channel claims, or other
settlement information to the other connector.
The amount should indicate the additional value of this settlement state (compared to the
previous settlement state), in a unit that was agreed out-of-band.

- `Response` is returned if the peer acknowledges the `Transfer`. This means
  the transfer is now completed and has been applied to the balance. If a
`Response` has been returned, balances MUST have been updated.

- `Error` is returned if the peer does not accept the transfer. This could be
  because some protocol data are malformed, or because the peer believes that
the sender's balance is insufficient. If an `Error` has been returned, the peer
MUST NOT have updated their balance.
