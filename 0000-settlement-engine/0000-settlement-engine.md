---
title: Settlement Engine
draft: 1
---

# Settlement Engine

## Conventions

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://tools.ietf.org/html/rfc2119).

## Overview

This specification codifies a common interface for a **settlement engine**. Settlement engines are services which perform two primary operations:

1. Send payments: execute outgoing settlements
2. Receive payments: acknowledge incoming settlements

Counterparties may operate compatible settlement engines to settle their liabilities between one another. Different implementations may utilize different settlement systems or types of settlements, such as:

- Sending money or assets to the counterparty
- Transferring value on a shared ledger
- Signing and exchanging payment channel claims
- Performing a task for the counterparty with a mutually ascribed value

## Usage in Interledger

### Interledger packet flow

In the [Interledger protocol](../0001-interledger-architecture/0001-interledger-architecture.md), a **peer** is a connector who is a counterparty to another connector. Connectors clear and fulfill ILP packets with their peers, which represent conditional IOUs that affect their mutual accounting relationships.

A connector may extend a given peer a limited line of credit, or none at all, depending upon their trustworthiness. As the connector receives incoming ILP PREPARE packets from a peer, forwards them, and returns corresponding ILP FULFILL packets, that peer's liabilities to the connector accrue. If the peer's liabilities exceed the credit limit assigned to it, the connector may reject and decline to forward additional packets.

In order to continue transacting, the peer must settle their liabilities. In most cases, this is accomplished through sending a payment on a settlement system that both peers have agreed to use. The connector should acknowledge the incoming payment&mdash;irrevocably discharging some liability the peer owed to it&mdash;and enabling it to clear and forward subsequent packets from the peer on credit.

Settlement engines provide a standardized mechanism for Interledger connectors to coordinate and reconcile these settlements.

### Accounting

An **account** represents a record of transactions between counterparties, denominated in some fungible asset. Each account may be comprised of multiple account balances, which each represent the net difference between amounts received (credits) and amounts owed (debits) for some subset of the transactions.

Interledger connectors are RECOMMENDED to operate an **accounting system** which keeps a record of two balances for each account:

- **Accounts payable**, the amount owed by the connector to its peer for packets its peer has fulfilled.
  - Positive amount indicates the connector is indebted to its peer (a _liability_ for the connector).
  - Negative amount indicates the connector has prefunded.
- **Accounts receivable**, the amount owed to the connector by its peer for packets the connector has fulfilled.
  - Positive amount indicates its peer is indebted to the connector (an _asset_ to the connector).
  - Negative amount indicates its peer has prefunded.

(Note: in context of "accounts payable" or "accounts receivable," "accounts" actually refers to a single account balance, not multiple accounts.)

Thus, the connector's accounts payable with its peer should mirror its peer's accounts receivable with the connector, and respectively, the connector's accounts receivable should equal its peer's accounts payable.

### Settlement

A **settlement** is the irrevocable discharge of a liability by providing something of value to the party to whom the liability is owed.

Settlements may be performed by using a **settlement system**, or medium for exchanging value. Some settlements may transfer funds on a **ledger**, or registry of account balances and/or transactions, which is a type of settlement system. (Although not all settlement systems are ledgers, here, the terms are sometimes used interchangeably.)

Settlement systems include, but are not limited to:

- Cryptocurrencies/distributed ledgers
- Payment channel networks built on blockchains
- Bank clearing houses
- Credit card processors
- Money transfer services

TODO Flesh out examples of settlements/settlement systmes

TODO Explain that settlement is triggered by the accounting system

TODO Should the expected netting behavior be included?

### Double-entry bookkeeping

The interface in this specification provides a mechanism to reconcile settled cash balances, representing _value_, with the aforementioned account balances tracked by the accounting system, representing _credit_.

Together, a settlement engine and an accounting system interface with one another to perform double-entry bookkeeping.

To ensure accurate double-entry bookkeeping, settlement engine and accounting system implementations MUST enforce several core guarantees.

#### Accounting System Guarantees

##### Account for outgoing settlements

If the accounting system opts to trigger a settlement:

1. The accounting system MUST debit the accounts payable, subtracing the amount of the settlement.
2. Then, the accounting system MUST send a request to the settlement engine to settle the amount.

If the settlement engine responds that it only queued a partial amount for settlement (due to lesser precision), the accounting system MUST credit back the accounts payable, adding the leftover amount.

If request retries fail per the [idempotency rules](#idempotency), the accounting system MUST credit back the accounts payable, adding the amount of the failed settlement.

##### Account for incoming settlements

If the settlement engine instructs the accounting system a settlement was received, the accounting system MUST credit the accounts receivable, subtracting the amount of the settlement.

#### Settlement Engine Guarantees

##### Retry crediting incoming settlements

After the settlement engine requests the accounting system to credit an incoming settlement, if the accounting system responds that it only credited a partial amount (due to lesser precision), the settlement engine MUST track the leftover amount to retry later.

If the request fails after several attempts per the [idempotency rules](#idempotency), the settlement engine MUST track the failed amount to retry later.

TODO clarify "retry later" means "when subsequent settlements are received, prompting another notification"

##### Settlement symmetry

Given two non-malicious peers transacting under normal conditions, compatible settlement engine implementations MUST ensure outgoing settlements from one peer are eventually acknowledged as incoming settlements by the other.

More formally, the sum of amounts one settlement engine instance is instructed to settle MUST eventually equal the sum of amounts the peer's settlement engine instance instructs its accounting system to credit as incoming settlements.

Varying external conditions, such as connectivity between peers or settlement system latency, MAY delay or prevent consistency of these instructed and acknowledged settlements.

#### Trade-offs of aynchronous settlement

TODO Explain the rationale for the async balance model/why it's okay if the settlement engine fails

### Bilateral communication

In order to settle or receive settlements with a peer, a settlement engine may first need to retrieve or communicate information with the peer's settlement engine. Two peered settlement engine instances may send and receive settlement-related messages among themselves, such as idenifiers for their ledger accounts, payment channel claims, or to negotiate fees.

Interledger connectors use a transport, such as HTTP or WebSockets, to send and receive data with peers. Settlement engine implementations SHOULD proxy all messages through services operated by its Interledger connector leveraging its existing transport to forward settlement messages to its peer's connector and peer's settlement engine.

#### The Flow

1. Origin settlement engine sends a callback request to its connector with the settlement-related message to forward.
2. Origin connector forwards the message to the peer's connector using its existing transport.
3. Peer connector receives the message, identifies which settlement engine instance the account is associated with, and sends a request to its settlement engine to handle the message.
4. Peer settlement engine processes the message and responds with its own message.
5. Peer connector sends the response message back across the transport channel to the origin connector.
6. Origin connector sends the response message back to the origin settlement engine.

#### Usage with [ILP-over-HTTP](../0035-ilp-over-http/0035-ilp-over-http.md)

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

Each account MUST be identified by a unique, [URL-safe](https://tools.ietf.org/html/rfc3986#section-2.3) string.

The settlement engine MUST be responsible for correlating an account identifier to the peer's identity on the shared ledger or settlement system, if required. For separation of concerns between clearing and settlement, the accounting system is NOT RECOMMENDED to have knowledge of the peer's identity on the shared settlement system.

### Units and quantities

An amount of a given asset or currency may be represented using different denominations or units of the asset. For example, one U.S. dollar may be represented as \$1 or 100 cents, and one Bitcoin may be represented as 1 BTC or 100000000 satoshis.

A **standard unit** is the typical unit of value for a particular asset, such as \$1 in the case of U.S. dollars, or 1 BTC in the case of Bitcoin.

A **fractional unit** represents some unit smaller than the standard unit, but with greater precision. Examples of fractional monetary units include one cent (\$0.01 USD), or 1 satoshi (0.00000001 BTC).

An **asset scale** is the difference in orders of magnitude between a **standard unit** and a corresponding **fractional unit**. More formally, the asset scale is a non-negative integer (0, 1, 2, …) such that one **standard unit** equals `10^(-scale)` of a corresponding **fractional unit**. If the fractional unit equals the standard unit, then the asset scale is 0.

For example, one cent represents an asset scale of 2 in the case of USD, whereas 1 satoshi represents an asset scale of 8 in the case of Bitcoin.

#### `Quantity` JSON type

A quantity represents an amount denominated in some unit of a particular fungible asset. (Since account balances may only be denominated in a single asset, the type of asset should be implicit).

##### Attributes

- **`amount`** string
  - Number of the given unit of the asset between 0 and the maximum 64-bit unsigned integer, 18,446,744,073,709,551,615 (inclusive).
  - The amount is encoded as a string to ensure no precision is lost on platforms that don't natively support full precision 64-bit integers.
- **`scale`** number
  - Represents an _asset scale_ as defined in the previous section.

##### Example

To represent $2.54 in units of cents, where the amount is a multiple of $0.01:

```json
{
  "amount": "254",
  "scale": 2
}
```

#### Scale conversions

If the accounting system or settlement engine receives a request with a **[`Quantity`](#quantity-type)** denominated in a unit more precise than its unit, it MUST convert the quantity into its native unit. If so, the resulting amount MUST be rounded down before fulfilling the request.

The response to the request MUST include the converted, rounded **[`Quantity`](#quantity-type)** used to fulfill the request, which MUST be less than or equal to the amount sent in the original request.

Then, the system with the additional precision initiating the request MUST track the leftover sum so it may accumulate and be retried in subsequent requests.

#### Choosing scales

All quantities the settlement engine includes in its responses or callback requests MUST use the same unit its settlements are denominated in, which is typically the smallest denomination of the asset on the settlement system.

The accounting system is RECOMMENDED to use the same unit or scale as the settlement engine to minimize conversion inconsistencies.

### Settlement Engine HTTP API

Settlement engines MUST implement these endpoints.

#### Initiate an account

Inform the settlement engine that a new accounting relationship was instantiated. The settlement engine MAY perform tasks as a prerequisite to settle the new account. For example, a settlement engine implementation might send messages to the peer to exchange ledger identifiers or to negotiate terms of the settlement arrangement.

##### Request

```http
POST /accounts HTTP/1.1
Content-Type: application/json
```

> ```json
> {
>   id: <account identifier>
> }
> ```

##### Response

```http
HTTP/1.1 201 CREATED
```

#### Perform outgoing settlement

Settle a liability owed to the peer for the given amount.

Note that the settlement engine MAY accrue owed settlements without settling immediately due to varying arrangements, implementations, or conditions. The settlement engine SHOULD persist amounts owed to the peer that have yet to be settled so they can be settled later.

The accounting system MUST be the only entity invoking this instruction and MUST preemptively debit this amount from the accounts payable, or some liability account tracking a balance owed to the peer, to ensure accurate accounting.

##### Request

```http
POST /accounts/:id/settlements HTTP/1.1
Accept: application/json
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** to settle
>
> - If the amount is `0`, the settlement engine MAY retry failed settlements.

##### Response

```http
HTTP/1.1 202 ACCEPTED
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** enqueued to settle
>
> - This response indicates the given amount will eventually be settled, but does not guarantee that a settlement was executed.
> - The amount enqueued to settle MUST always be less than or equal to the quantity in the original request.
> - If the quantity enqueued to settle is less than the quantity of the original request, the accounting system MUST credit the leftover amount back to the accounts payable, or the same liability account tracking a balance owed to the peer. This is to prevent the systems getting out-of-sync if the settlement engine uses a unit less precise than the accounting system's unit.

#### Handle incoming request

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

#### Complete specification

<details>
  <summary>The full settlement engine HTTP API, including all response codes, error codes, and additional endpoints for manual management are available in this Swagger definition.</summary>

```
TODO Embed the definition here
```

</details>

Settlement engine implementations are RECOMMENDED to implement the standardized endpoints for manual management noted above.

#### Additional RPCs

Settlement engine implementations MAY expose additional, non-standard endpoints for manual operations or configuration.

For example, settlement engines that use payment channels may expose functionality to manually open, fund, and close channels.

### Settlement Engine Callback HTTP API

Settlement engine implementations MUST implement the following callbacks.

#### Receipt of incoming settlement

Settlement engine implementations SHOULD send a callback request to this endpoint when incoming settlements are received. The endpoint handling the call, such as an accounting system, SHOULD credit the amount of the settlement to an account balance to ensure accurate double-entry bookkeeping.

##### Request

```http
POST /accounts/:id/settlements HTTP/1.1
Accept: application/json
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** that should be credited to the account as an incoming settlement

##### Response

```http
HTTP/1.1 201 CREATED
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** credited to the account
>
> - The amount credited MUST always be less than or equal to the quantity in the original request.
> - If the quantity credited is less than the quantity of the original request, the settlement engine MUST track the leftover amount so it may accumulate and be added to subsequent notifications to prevent the two systems getting out-of-sync.

#### Send outgoing request

Send a message to given peer's settlement engine and return its response.

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

### Idempotency

TODO Good reference: https://stripe.com/blog/idempotency

TODO "fault tolerant"

Implementations MUST support [idempotency](https://en.wikipedia.org/wiki/Idempotence) for safely retrying requests without accidentally performing the same operation multiple times. This is useful when an API call is disrupted in transit and you do not receive a response. For example, if a request to send a settlement does not respond due to a network connection error, you can retry the request with the same idempotency key to guarantee that no more than one settlement is performed.

#### Performing idempotent requests

All `POST` requests MUST supply idempotency keys by providing an additional `Idempotency-Key: <key>` header with the request.

For each unique request, such as an individual settlement, a unique key should be generated. The key MUST generated with a cryptographically secure pseudorandom number generator to avoid collisions. Implementations are RECOMMENDED to use a v4 UUID.

TODO

#### Recommended retry behavior

TODO

#### Handling idempotent requests

All `POST` endpoints MUST support idempotency keys.

TODO
