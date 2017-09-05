# Common Ledger Protocol (CLP)

## Preface

This document describes the Common Ledger Protocol (CLP), a ledger protocol for
bilateral liquidity relationships. It is similar in function to [Plugin RPC],
but has been rewritten to use OER instead of JSON, and extensibility features
have been added.

## Introduction

### Motivation

There are many different types of ledgers, and Interledger aims to interoperate
all of them. For fast ledgers that support hashlocks, it is enough to wrap the
ledger's API in a [Ledger Plugin]. These allow you to send interledger payments
through anyone else on that ledger who is running your plugin.

In lots of scenarios, we don't have an underlying ledger that's fast enough to
do every ILP payment on-ledger. There are also many situations when two parties
trust one another up to an amount, and don't need any third-party ledger to
book-keep for them. Currently, this need is filled by [ILP Plugin Virtual],
which uses [Plugin RPC] as its ledger protocol. JSON messages are passed back
and forth to perform transfers and send quote requests. Custom JSON messages
can be added to extend the Plugin RPC messages, but they aren't well defined.

Because the use case for a bilateral ledger protocols is so ubiquitous, the CLP
has been invented to make the protocol extensible, efficient, and friendly to
re-implementation.

### Scope

The CLP, despite its name, is just another ledger protocol. It manages
conditional transfers, messaging requests, and allows [side protocols] for
extensibility. You can use ILP without using CLP. CLP is intended to be a
well-suited solution so that a new bilateral ledger protocol doesn't need to
exist for every new use case.

This document describes the flow and messages that CLP uses. It does not cover
establishment of CLP channels, nor does it cover any side protocols.  Side
protocols include functionality like ledger metadata, balance, automated
settlement, and dispute resolution. 

The CLP Packet format is described exactly in the [CLP ASN.1 spec].

## Terminology

- **CLP** is the common ledger protocol, as described by this packet and the
  ASN.1 spec.

- A **Side Protocol** is a protocol which isn't defined by CLP and is carried
  in the side protocol data (see below).

- A **CLP Connection** is a websocket connection over which CLP Packets are
  sent.

- **CLP Packets** are the messages defined in the CLP ASN.1 spec.

- **Peers** are the parties on a CLP connection. Your peer is the party on the
  other side of the CLP connection.

- The **Bilateral Ledger** is the ledger which a CLP connection controls.  The
  bilateral ledger is a persistent log of CLP packets, which can be used to
deduce the current balance between two peers and the state of all transfers
between them.

- **Authoritative State** means that the entire Bilateral Ledger is being
  tracked by a party. Both peers on a CLP connection can keep authoritative
state, which means they can get into dispute if they disagree on the state of a
transfer. This usually happens when network latency causes the peers to
disagree about expiries. If one party keeps authoritative state, the other
party must trust them not to tamper with it.

## Overview

CLP is broken up into 4 different RPC requests, which can get 2 different
responses. Every CLP packet follows a common structure:

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
1 | Side Protocol |
2 | Count (5)     |
  +---------------+
  | Side Protocol |
  | Data          |
  . (6)           |
  .               |
  .               |
  |               |
  +---------------+
```

1. **Type**: A 1-byte value describing what type of CLP packet this is.
The [CLP ASN.1 spec] describes what the different type IDs mean.

2. **Request ID**: A 4-byte value used to correlate this requests and
responses.

3. **Length Prefix**: A 1-byte (if under 128) or 2-byte value, containing the
combined length of the packet-specific data and side protocol data sections.

4. **Packet-Specific Data:** Fields specific to the type of CLP packet. Variable
length.

5. **Side Protocol Count:** Variable-length integer containing the number of
side protocols carried by this packet.

5. **Side Protocol Data:** A list of key-value pairs, where the key is a
length-prefixed ascii string, and the value is a length-prefixed octet string.
The key signifies the side protocol's name, and the value is the data.

## Flow

CLP uses a simple RPC flow. A request-type CLP packet is sent, and a
response-type CLP packet is sent in response with the same request ID.

If a malformed CLP packet is sent, there should be no response. If a
response-type CLP packet is sent without matching a previous request, it should
be ignored.  If a request has already been responded to and another response is
sent, the second response should be ignored.

Because it would be too slow to atomically save all requestIds that are
processed, they are not idempotent. It is the responsibility of the requestor
to make sure they don't duplicate requestIds. The implementation should ensure
that no two in-flight requests are sent out with the same requestId. The
responder should always send back a response to a request with the same
requestId.

The request types are `Message`, `Prepare`, `Fulfill` and `Reject`, and the
response types are `Ack` (which may be [removed]), `Response`, and `Error`.

### Message

`Message` is used for sending information to the peer. It contains no message
data, only side protocol data. ILQP packets are attached under the protocol
`ilp`.

#### Response

- `Response` is returned if the peer acknowledges the `Message`. If the peer
  has data to send in reply (e.g. a quote response), it is carried in the side
protocol data.

- `Error` is returned if the peer is not able to process the message, or there
  was an unexpected error and further messages should not be sent.

### Prepare

`Prepare` is used to create a transfer on the bilateral ledger. The message
data contains `transferId`, `amount`, `executionCondition`, and `expiresAt`.
`Prepare` is a request with side effects, because it creates a transfer with
the given details. This transfer begins in the `prepared` state.

`transferId` is a 128-bit unique ID that references the transfer. `amount` is
a 64-bit integer denominated in ledger base units. The ledger base units can be
anything, so long as both parties on the bilateral ledger agree on their
meaning. Examples of base units are "micro-XRP," "satoshi," or "nano-dollars
settled over paypal." `executionCondition` is a 256-bit integer containing the
SHA-256 hash of this conditional transfer's fulfillment.  `expiresAt` is a
ASN.1 UTC GeneralizedTime containing the expiry of this transfer.

ILP payment packets are attached to the side protocol data under the protocol
`ilp`. 

#### Response

- `Response` is returned if the peer acknowledges the `Prepare`. This means the
  transfer is now `prepared` and has been applied to the balance. It may carry
side protocol data, for example a payment channel claim.

- `Error` is returned if the peer does not accept the transfer. This could be
  because it is incompatible with an existing transfer with the same ID (see
Idempotency below), or because it exceeds some constraint your peer has placed.
The amount could be too high, or could exceeds the balance.

#### Idempotency

If a transfer with the given ID already exists in any state, a new transfer
should not be created. If the packet (including side protocol data) matches an
existing transfer exactly and that transfer is in the `prepared` state, a
`Response` should be returned. If the packet (including side protocol data) shares
the ID of an existing transfer but other details do not match, an `Error`
should be returned. If the packet (including side protocol data) exactly
matches an existing transfer but that transfer is in the `fulfilled` state or
the `rejected` state, an `Error` should be returned.

#### Expiry

After the `expiresAt` date is reached, the transfer can no longer be fulfilled.
If one party on the CLP connection is keeping authoritative state, they should
send a `Reject` request to the other party. If both parties are keeping
authoritative state, they can independently expire the transfer (set the state
to `rejected` and roll it back) automatically.

### Fulfill

`Fulfill` is used to change an existing transfer from the `prepared` state to
the `fulfilled` state. The packet-specific data of `Fulfill` is made up of `transferId`
and `fulfillment`. `Fulfill` is a request with side effects: it changes the
state of the transfer and finalizes the transfer's balance update. If the
transfer is already fulfilled, no changes are applied.

`transferId` is a 128-bit unique ID, which references an existing transfer.
`fulfillment` is a 256-bit integer, containing the preimage of the
`executionCondition` of the referenced transfer.

#### Response

A `Fulfill` request must be sent from the receiver of the referenced transfer,
not the sender.

A `Fulfill` request is successful if `transferId` references an existing
transfer in the `prepared` state, the `fulfillment` is the SHA-256 preimage of
the referenced transfer's `executionCondition`, and the current time is before
the referenced transfer's `expiresAt`.

A `Fulfill` request is also successful if the transfer is in the `fulfilled`
state, and this packet matches the one that fulfilled the transfer,
including side protocols but not including requestId.

- `Response` is returned if the request is successful.  data to be passed back.
  This means the transfer's state is now `fulfilled`, and its balance change
has been finalized.

- `Error` is returned if there is no transfer with the given ID, the
  fulfillment does not match the condition, the expiresAt has already passed,
or the transfer has been `rejected`.

### Reject

`Reject` is used to change an existing transfer from the `prepared`
state to the `rejected` state. The packet-specific data of `Reject` is made up
of `transferId` and `rejectionReason`.

`transferId` is a 128-bit unique ID, which references an existing transfer.
`rejectionReason` is an [ILP Error], containing the reason that this transfer
was rejected.

#### Response

A `Reject` request must come from the receiver of the referenced transfer,
not the sender.

A `Reject` request is successful if `transferId` references an existing
transfer in the `prepared` state.

A `Reject` request is also successful if `transferId` references an existing
transfer in the `rejected` state, and this packet matches the one that
rejected this transfer, including side protocols but not including requestId.

- A `Response` is returned if the request is successful. This indicates that
  the balance changes of the referenced transfer have been rolled back.

- An `Error` is returned if the request was not successful. _TODO: create
  error codes that distinguish the different failure cases_.
