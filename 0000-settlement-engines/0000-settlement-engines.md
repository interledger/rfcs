---
title: Settlement Engines
draft: 1
---

# Settlement Engines

## Conventions

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://tools.ietf.org/html/rfc2119).

## Overview

This specification codifies a common interface for **settlement engines**. Settlement engines are services which perform two primary operations:

1. Send payments: execute outgoing settlements
2. Receive payments: acknowledge incoming settlements

Counterparties may operate compatible settlement engines to settle their liabilities between one another. Different implementations may utilize different settlement systems or types of settlements, such as:

- Sending money or assets to the counterparty
- Transferring value on a shared ledger
- Signing and exchanging payment channel claims
- Performing a task for the counterparty with a mutually ascribed value

## Usage in Interledger

### Interledger packet flow

In the [Interledger protocol](../0001-interledger-architecture/0001-interledger-architecture.md), a **peer** is a connector who is a counterparty to another connector. An **account** is the connector's relationship with the counterparty, representing their arrangement to transact with one another. Connectors clear and fulfill ILP packets with their peers, which represent conditional IOUs that affect these accounts.

A connector may extend a given peer a limited line of credit, or none at all, depending upon their trustworthiness. As the connector receives incoming ILP PREPARE packets from a peer, forwards them, and returns corresponding ILP FULFILL packets, that peer's liabilities to the connector accrue. If the peer's liabilities exceed the credit limit assigned to it, the connector may reject and decline to forward additional packets.

In order to continue transacting, the peer must settle their liabilities. In most cases, this is accomplished through sending a payment on a settlement system that both peers have agreed to use. The connector should acknowledge the incoming payment&mdash;irrevocably discharging some liability the peer owed to it&mdash;and enabling it to clear and forward subsequent packets from the peer on credit.

Settlement engines provide a standardized mechanism for Interledger connectors to coordinate and reconcile these settlements.

### Accounting

Connectors MUST record their transactions with peers and/or the effects of their transactions with peers through the process of accounting.

In this accounting context, an **account** represents amounts received (credits) and amounts owed (debits) for a set of transactions between counterparties. The **balance** of an account is the net difference between these credits and debits. All the balances and transactions of an account are denominated in a single, fungible asset.

Interledger connectors are RECOMMENDED to operate an **accounting system** which keeps a record of two accounts for each peer:

- **Accounts payable**, the amount owed by the connector to its peer for packets its peer has fulfilled.
  - Positive amount indicates the connector is indebted to its peer (a _liability_ for the connector).
  - Negative amount indicates the connector has sent a pre-payment to its peer.
- **Accounts receivable**, the amount owed to the connector by its peer for packets the connector has fulfilled.
  - Positive amount indicates its peer is indebted to the connector (an _asset_ to the connector).
  - Negative amount indicates its peer has sent a pre-payment to the connector.

(Note that "accounts payable" and "accounts receivable" refer to accounts as _records_, distinct from accounts referring to the _arrangement_ between counterparties.)

Thus, the connector's accounts payable with its peer should mirror its peer's accounts receivable with the connector, and respectively, the connector's accounts receivable should equal its peer's accounts payable.

### Settlement

A **settlement** is the irrevocable discharge of a liability by providing something of value to the party to whom the liability is owed.

Settlements may occur on a **settlement system**, or medium for exchanging value. Some settlements may transfer funds on a **ledger**, or registry of account balances and/or transactions, which is a type of settlement system. (Although not all settlement systems are ledgers, here, the terms are sometimes used interchangeably.)

Examples of settlement systems include:

- Cryptocurrencies, blockchains, and distributed ledgers
- Payment channels and layer 2 networks
- Bank clearing houses
- Credit card processors
- Money transfer services
- Cash or physical delivery of assets

The accounting system is responsible for triggering settlements, which may be based on the TODO liabilities owed the peer.

### Double-entry bookkeeping

The interface in this specification provides a mechanism to reconcile settled cash balances, representing _value_, with the aforementioned account balances tracked by the accounting system, representing _credit_.

Together, a settlement engine and an accounting system interface with one another to perform double-entry bookkeeping.

To ensure accurate, balanced double-entry bookkeeping, settlement engine and accounting system implementations MUST enforce several invariants.

#### Settlement engine invariants

##### Settlement symmetry

Individual settlement engine implementations define how value is transferred to the counterparty: this specification merely defines settlements in terms of how settlement engines behave. TODO

The fundamental expected behavior of a settlement engine implementation is the sum of amounts one instance is instructed to settle eventually equals the sum of amounts the recipient instance instructs its accounting system to credit as incoming settlements.

Many factors may cause temporary or lasting inconsistencies between these instructed and acknowledged settlements. For example:

- External conditions, such as the time to finalize settlements on an underlying ledger
- Unintended bugs in the settlement engine implementation
- Intended settlement engine behavior, such as accruing owed balance to cover a fee
- Malicious peers or peers using incompatible settlement engines

As long as the instructed settlements do not equal the acknowledged settlements, the double-entry bookkeeping is out-of-balance.

##### Track uncredited incoming settlements

After the settlement engine requests the accounting system to credit an incoming settlement, if the accounting system responds that it only credited a partial amount (due to lesser precision), the settlement engine MUST track the uncredited leftover amount.

If the request fails after retrying per the [idempotence rules](#idempotence), the settlement engine MUST track the uncredited amount to retry later.

When a subsequent settlement is received, the settlement engine MUST request the accounting system to credit a new incoming settlement for the total amount yet to be credited, including the leftover amount(s).

#### Accounting system invariants

##### Account for outgoing settlements

If the accounting system opts to trigger a settlement:

1. The accounting system MUST debit the accounts payable, subtracing the amount of the settlement.
2. Then, the accounting system MUST send a request to the settlement engine to settle the amount.

If the settlement engine responds that it only queued a partial amount for settlement (due to lesser precision), the accounting system MUST credit back the accounts payable, adding the leftover amount.

If request retries fail per the [idempotence rules](#idempotence), the accounting system MUST credit back the accounts payable, adding the amount of the failed settlement.

##### Account for incoming settlements

If the settlement engine instructs the accounting system a settlement was received, the accounting system MUST credit the accounts receivable, subtracting the amount of the settlement.

#### Asynchronous design

To trigger a settlement, the accounting system optimistically debits the accounts payable before the settlement has been initiated. For a period of time, the accounts payable of the peer sending the settlement is inconsistent with the accounts receivable of the peer who will later receive the settlement.

Nonetheless, the bookkeeping is correct because the settlement engine tracks the owed balance if the settlement fails: it's merely the representations of the balances within the two peers' accounting systems that are temporarily inconsistent.

This asynchronicity was determined to be an acceptable trade-off instead of refunding failed settlements back to the accounts payable.

Since the settlement engine tracks the amounts of settlements that fail, if the conditions change so the settlement engine is later able to settle, a new settlement attempt may safely begin immediately. By contrast, if the failed settlement was credited back to the accounts payable, enabling the settlement engine to safely trigger new settlements would necessitate a more complex API.

Refunding failed settlements does enable those amounts to be netted against packets fulfilled in the opposite direction. However, if settlement continues to fail, the credit limit will eventually be breached and prevent the peers from transacting, negating this utility.

### Exchanging messages

In order to settle or receive settlements with a peer, a settlement engine may first need to retrieve or communicate information with the peer's settlement engine. Two peered settlement engine instances may send and receive settlement-related messages among themselves, such as identifiers for their ledger accounts.

To support multiple interoperable settlement engine implementations for a particular settlement system, implementators may standardize the schema and type of messages their settlement engines use to communicate with one another. This work is out-of-scope of this RFC.

#### Usage with [ILP-over-HTTP](../0035-ilp-over-http/0035-ilp-over-http.md)

Interledger connectors use a transport, such as HTTP or WebSockets, to send and receive data with peers. Settlement engine implementations SHOULD proxy all messages through its Interledger connector's existing transport like so:

1. Origin settlement engine sends a callback request to its connector with the settlement-related message to forward.
2. Origin connector forwards the message to the peer's connector using its existing transport.
3. Peer connector receives the message, identifies which settlement engine instance the account is associated with, and sends a request to its settlement engine to handle the message.
4. Peer settlement engine processes the message and responds with its own message.
5. Peer connector sends the response message back across the transport channel to the origin connector.
6. Origin connector sends the response message back to the origin settlement engine.

When a connector receives a request to send a message to the peer, the raw message from the settlement engine MUST be encoded within an ILP PREPARE packet as described below. Then, the ILP PREPARE should be sent to the peer's connector associated with the account using ILP-over-HTTP.

The peer's connector MUST extract the message data and forward it to its settlement engine for processing, and MUST NOT forward the ILP packet to any other connectors. When the settlement engine responds with a response message, the connector MUST encode the raw message from the settlement engine within an ILP FULFILL or ILP REJECT, depending upon the code of the response. If the connector was unable to process the request, it MUST respond with an ILP REJECT.

##### PREPARE

- `amount`: `0`
- `expiresAt`: _Determined by connector_
- `executionCondition`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `destination`: `peer.settle`
- `data`: _Request message from sender settlement engine_

##### FULFILL

- `fulfillment`: `0000000000000000000000000000000000000000000000000000000000000000`
- `data`: _Response message from recipient settlement engine_

##### REJECT

- `code`: _Determined by connector from HTTP status of forwarded request_
- `triggeredBy`: `peer.settle`
- `message`: _Determined by connector_
- `data`: _Response message from recipient settlement engine, or empty if antecedent failure_

### Motivation

Settlement engines supercede the [Ledger Plugin Interface (LPIv2)](../deprecated/0024-ledger-plugin-interface-2/0024-ledger-plugin-interface-2.md), an earlier abstraction for settlement integrations with Interledger. This new model addresses these issues:

1. Multi-account plugins required logic for handling ILP packets, increasing implementation complexity.
2. Plugins bundled settlement and bilateral communication functionality together, limiting composability.
3. JavaScript plugins limited interoperability with non-JavaScript connector implementations.
4. Plugins operated in the same process as the connector, which limited scaling the two services independently.

## Specification

### Accounts and identifiers

Each account MUST be identified by a unique, [URL-safe](https://tools.ietf.org/html/rfc3986#section-2.3) string, linked for the lifetime of the account.

The settlement engine MUST be responsible for correlating an account identifier to the peer's identity on the shared ledger or settlement system, if required. For separation of concerns between clearing and settlement, the accounting system is NOT RECOMMENDED to have knowledge of the peer's identity on the shared settlement system.

### Units and quantities

Asset amounts may be represented using any arbitrary denomination. For example, one U.S. dollar may be represented as \$1 or 100 cents, each of which is equivalent in value. Likewise, one Bitcoin may be represented as 1 BTC or 100,000,000 satoshis.

A **standard unit** is the typical unit of value for a particular asset, such as \$1 in the case of U.S. dollars, or 1 BTC in the case of Bitcoin.

A **fractional unit** represents some unit smaller than the standard unit, but with greater precision. Examples of fractional monetary units include one cent (\$0.01 USD), or 1 satoshi (0.00000001 BTC).

An **asset scale** is the difference in orders of magnitude between a standard unit and a corresponding fractional unit. More formally, the asset scale is a non-negative integer (0, 1, 2, …) such that one standard unit equals `10^(-scale)` of a corresponding fractional unit. If the fractional unit equals the standard unit, then the asset scale is 0.

For example, one cent represents an asset scale of 2 in the case of USD, whereas 1 satoshi represents an asset scale of 8 in the case of Bitcoin.

#### Selecting scales

Settlement engines are RECOMMENDED to perform or fulfill requests with amounts denominated in the same scale as its settlements.

Account balances within the accounting systems are RECOMMENDED to be denominated in the same scale as their corresponding settlement engine, but MAY use different ones. For example, micropayments may require more precision than can actually be settled, or databases may limit precision to less than the settlement system is capable of.

#### `Quantity` object

Represents an amount denominated in some unit of a particular fungible asset. (Since account balances may only be denominated in a single asset, the type of asset should be implicit).

##### Attributes

- **`amount`** &mdash; string
  - Quantity of the unit, which is a non-negative integer.
  - This amount is encoded as a string to ensure no precision is lost on platforms that don't natively support arbitrary precision integers.
- **`scale`** &mdash; number
  - Asset scale of the unit, between `0` and the maximum 8-bit unsigned integer, `255` (inclusive).

##### Example

To represent $2.54 in units of cents, where the amount is a multiple of $0.01:

```json
{
  "amount": "254",
  "scale": 2
}
```

#### Scale conversions

If the accounting system or settlement engine receives a request with a **[`Quantity`](#quantity-json-type)** denominated in a unit more precise than its unit, it MUST convert the quantity into its native unit. If so, the resulting amount MUST be rounded down before fulfilling the request.

The response to the request MUST include the converted, rounded **[`Quantity`](#quantity-json-type)** used to fulfill the request, which MUST be less than or equal to the amount sent in the original request. (If the amount rounds down to 0, this this amount MAY be 0.)

Then, the system with the additional precision initiating the request MUST track the leftover sum so it may accumulate and be retried in subsequent requests.

### Settlement Engine HTTP API

Settlement engines MUST implement these endpoints.

#### `AccountData` object

TODO Spec out these and ensure the naming is consistent

- "sendMessageCallbackUrl"
- "creditSettlementCallbackUrl"

#### Initiate an account

Inform the settlement engine that a new accounting relationship was instantiated. The settlement engine MAY perform tasks as a prerequisite to settle the new account. For example, a settlement engine implementation might send messages to the peer to exchange ledger identifiers or to negotiate settlement-related fees.

##### Request

```http
PUT /accounts/:id HTTP/1.1
```

##### Response

```http
HTTP/1.1 201 CREATED
```

#### Retrieve an account

##### Request

##### Response

#### Update an account

##### Request

```http
PUT /accounts/:id HTTP/1.1
Accept: application/json
Content-Type: application/json
```

TODO paylaod

##### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json
```

TODO payload

#### Delete an account

TODO Should deleting an account be an endpoint?

##### Request

```http
DELETE /accounts/:id HTTP/1.1
```

##### Response

```http
HTTP/1.1 204 No Content
```

#### Perform outgoing settlement

##### Request

The accounting system requests a settlement to occur with a particular account. The accounting system should [ensure accurate double-entry bookkeeping](#account-for-outgoing-settlements).

```http
POST /accounts/:id/settlements HTTP/1.1
Accept: application/json
Content-Type: application/json
Idempotency-Key: <key>
```

> **[`Quantity`](#quantity-json-type)** to settle

##### Response

The settlement engine should [asynchronously](#asynchronous-design) perform a [settlement](#settlement).

```http
HTTP/1.1 202 ACCEPTED
Content-Type: application/json
```

> **[`Quantity`](#quantity-json-type)** enqueued to settle, which is always less than or equal to the quantity in the original request

#### Handle incoming message

Respond to an incoming message from the given peer's settlement engine. The transport MUST be the only entity invoking this instruction.

##### Request

```http
POST /accounts/:id/messages HTTP/1.1
Accept: application/octet-stream
Content-Type: application/octet-stream
```

> _&lt;raw bytes of message&gt;_

##### Response

```http
HTTP/1.1 200 OK
Content-Type: application/octet-stream
```

> _&lt;raw bytes of response&gt;_

#### Additional RPCs

Settlement engine implementations MAY expose additional, non-standard endpoints for manual operations or other configuration.

### Settlement Engine Webhooks

Settlement engine implementations MUST implement the following callbacks.

#### Credit incoming settlement webhook

Settlement engine implementations MUST send a callback request to an account's `creditSettlementCallbackUrl` after an incoming settlement is received.

To ensure accurate double-entry bookkeeping, the endpoint handling the call, such as an accounting system, is RECOMMENDED to [account for the incoming settlement](#account-for-incoming-settlements).

##### Request

```http
POST <callbackUrl> HTTP/1.1
Accept: application/json
Content-Type: application/json
Idempotency-Key: <key>
```

> **[`Quantity`](#quantity-json-type)** to be credited to the account as an incoming settlement

##### Response

```http
HTTP/1.1 201 CREATED
Content-Type: application/json
```

> **[`Quantity`](#quantity-json-type)** credited to the account as an incoming settlement
>
> - The amount credited MUST always be less than or equal to the quantity in the original request.
> - If the quantity credited is less than the quantity of the original request, the settlement engine MUST track the leftover amount so it may accumulate and be added to subsequent notifications to prevent the two systems getting out-of-sync.

#### Send outgoing message webhook

Settlement engine implementations MUST send a callback request to an account's `sendMessageCallbackUrl` to send a settlement-related message to the peer's settlmenet engine.

To support messaging between peers, the endpoint handling the call SHOULD send the message to the peer's settlement engine and return its response.

TODO link to #usage-with-ilp-over-http

##### Request

```http
POST <callbackUrl> HTTP/1.1
Accept: application/octet-stream
Content-Type: application/octet-stream
```

> _&lt;raw bytes of message&gt;_

##### Response

```http
HTTP/1.1 200 OK
Content-Type: application/octet-stream
```

> _&lt;raw bytes of response&gt;_

### Idempotence

Idempotent requests ensure each side effect only happens once, even though the same request may be called multiple times. For example, if a request to perform a settlement fails due to a network connection error, [idempotence](https://en.wikipedia.org/wiki/Idempotence) prevents a client from accidentally triggering multiple settlements when it retries the request.

#### Performing idempotent requests

Requests to settle or requests to credit incoming settlements MUST include an idempotency key, or globally unique string, within an `Idempotency-Key: <key>` header. To avoid collisions, this key MUST be derived from a cryptographically secure source of randomness, such as a v4 UUID.

#### Recommended retry behavior

If the client receives no response, it MUST retry the request with the same idempotency key.

To prevent overwhelming the server, the client SHOULD exponentially backoff each retry attempt and add random "jitter" to vary the retry interval. After several failed attempts, the client MUST rollback any side effects it performed, such as [refunding balances](#double-entry-bookkeeping).

#### Handling idempotent requests

Endpoints to settle and endpoints to credit incoming settlements MUST support idempotency keys. Before an endpoint responds to the request with a new idempotency key (one it hasn't seen before), it should persist the idempotency key and the state of its response. If a subsequent request is sent with the same idempotency key, the server should use the state from the initial request to return the same response.

Servers MUST persist idempotency keys and response state for at least 24 hours after the initial request was performed.
