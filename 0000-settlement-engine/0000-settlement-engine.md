---
title: Settlement Engine
draft: 1
---

# Settlement Engine

## Conventions

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://tools.ietf.org/html/rfc2119).

## Overview

This specification codifies a common interface for a **settlement engine**. Settlement engines are services which perform two primary operations:

1. **Send payments**: execute outgoing settlements
2. **Credit payments**: acknowledge incoming settlements

**Peers**, or entities that transact with one another, may operate compatible settlement engines to settle their liabilities. Different implementations may utilize different settlement systems or types of settlements, such as:

- **Ledger transfers:** adjusting balances on an underlying shared ledger
- **Physical settlement:** delivering an asset to the counterparty
- **Payment channels:** sending a claim entitling the peer to an escrow
- Using a custom protocol to mututally agree to discharge a liability

## Usage in Interledger

Connectors using the [Interledger protocol](https://github.com/interledger/rfcs/tree/master/0001-interledger-architecture) clear and fulfill ILP packets with peers, which represent conditional IOUs that affect their mutual accounting relationships.

Connectors may extend some particular peer a limited line of credit (or none, if they're untrusted). As a connector receives incoming ILP PREPARE packets from a peer, forwards them, and returns corresponding ILP FULFILL packets, the peer's liabilities accrue. If the peer's liabilities to the connector exceeds the credit limit assigned to it, the connector may reject and decline to forward additional packets.

In order to continue transacting, the peer must settle their liabilities. In most cases, this is accomplished through sending a payment on a settlement system that both peers have in common. The connector should acknowledge the incoming payment&mdash;irrevocably discharging some liability the peer owed it&mdash;and enabling it to clear and forward subsequent packets on credit.

Settlement engines provide a standardized mechanism for Interledger connectors to coordinate and reconcile these settlements.

### Accounting

An **account** represents a record of transactions between two peers, denominated in some fungible asset. Each account may be comprised of multiple **account balances**, which each represent the net difference between amounts received (credits) and amounts owed (debits) for some subset of the transactions.

Interledger connectors are RECOMMENDED to operate an **accounting system** which keeps a record of two balances for each account:

- **Accounts payable**, the amount owed by the operator to the counterparty for outgoing obligations its counterparty has fulfilled.
  - Positive amount indicates the operator is indebted to its counterparty (a _liability_ for the operator).
  - Negative amount indicates the operator has prefunded.
- **Accounts receivable**, the amount owed to the operator by its counterparty for incoming obligations the operator has fulfilled.
  - Positive amount indicates its counterparty is indebted to the operator (an _asset_ to the operator).
  - Negative amount indicates its counterparty has prefunded.

(Note: in context of "accounts payable" or "accounts receivable," "accounts" actually refers to a single account balance, not multiple accounts.)

Thus, the connector's accounts payable with its peer should mirror its peer's accounts receivable with the connector, and respectively, the connector's accounts receivable should equal its peer's accounts payable.

The interface in this specification provides a mechanism to reconcile settled cash balances, representing _value_, with the aforementioned account balances tracked by the accounting system, representing _credit_.

Together, a settlement engine and an accounting system interface with one another to perform double-entry bookkeeping.

### Settlement

A **settlement** is the full and irrevocable discharge of an obligation. Settlements may be performed by using a **settlement system**, or medium for exchanging value.

A **ledger** is a registry of account balances and/or transactions. (Although not all settlement systems are ledgers, here, the terms are sometimes used interchangeably.)

TODO explain the below better

To ensure correct double-entry bookkeeping, several guarantees must be upheld:
- If the accounting system instructs the settlement engine to settle some amount:
  1. The accounting system MUST subtract the amount from the accounts payable.
  2. The settlement engine MUST eventually settle the amount.
- If the settlement engine receives an incoming settlement:
  1. The settlement engine MUST acknowledge the settlement to the accounting system.
  2. The accounting system MUST add the amount to the accounts receivable.

### Bilateral communication

Interledger connectors use a transport, such as HTTP or WebSockets, to send and receive ILP packets with peers.

To send messages or requests to the peer's settlement engine instance, settlement engine implementations SHOULD proxy all requests through a service operated by the connector. The connector will forward messages to the peer's connector using the shared transport, which will then send them to its settlement engine for processing. The peer settlement engine's response to the request will then be sent back, across the two connectors, to the origin settlement engine.

#### Usage with [ILP-over-HTTP](https://github.com/interledger/rfcs/blob/master/0035-ilp-over-http/0035-ilp-over-http.md)

To send the message to the peer, the raw message should be encoded in the `data` field of an ILP packet and addressed to `peer.settle`. The connector that receives the packet should identify the peer and send it to the settlement engine instanced associated with that account.

ILP packets intended for the peer to proxy to its settlement engine should be addressed to `peer.settle` and MUST NOT be forwarded to any subsequent connectors.

Connectors MUST track which settlement engine a peer's account is associated with and ensure their messages are delivered to that particular settlement engine.

### Motivation

Settlement engines supercede the [Ledger Plugin Interface (LPIv2)](https://github.com/interledger/rfcs/blob/master/0024-ledger-plugin-interface-2/0024-ledger-plugin-interface-2.md), an earlier abstraction for settlement integrations with Interledger. The new model addresses these issues:

1. Multi-account plugins required logic for handling ILP packets, increasing implementation complexity.
2. Plugins bundled settlement and bilateral communication functionality, limiting composability with other transports.
3. The JavaScript specific interface prevented connector implementations in other programming languages from using existing plugins.
4. Plugins operated in the same process as the connector, which limited scaling the two systems independently.

## Specification

### Core Functionality

All settlement engine implementations MUST functionally guarantee that **the sum of amounts a settlement engine instance is instructed to settle should eventually equal the sum of amounts the peer's settlement engine instance acknowledges receipt of.**

Varying implementations, arrangements, and conditions (such as connectivity to the settlement system) may delay consistency of instructed and acknowledged settlements by an indeterminate amount of time.

### Accounts and identifiers

Each account MUST be identified by a unique, URL-safe string.

#### Accounts vs ledger identities

The settlement engine MUST be responsible for correlating an account identifier to the peer's identity on the shared ledger or settlement system, if required.

For separation of concerns between the accounting system and the settlement system, the accounting system is NOT RECOMMENDED to have knowledge of the peer's identity on the shared settlement system, but rather only the account identifier described here.

### Units and quantities

A **monetary unit** is the standard unit of value of a particular currency or asset, such \$1 in the case of USD, or 1 BTC in the case of Bitcoin.

A **fractional monetary unit** is some unit smaller than the standard monetary unit with greater precision: for example, one cent (\$0.01) in the case of USD, or 1 satoshi (0.00000001 BTC) in the case of Bitcoin.

An **asset scale** for some fractional monetary unit is the difference in orders of magnitude between that unit and the standard monetary unit. More formally, a non-negative integer (0, 1, 2, …) such that one monetary unit equals `10^(-scale)` of the given fractional monetary unit, or 0 if the unit is the standard monetary unit.

For example, one cent represents an asset scale of 2 in the case of USD, whereas 1 satoshi represents an asset scale of 8 in the case of Bitcoin.

#### `Quantity` JSON type

A quantity represents an amount denominated in some unit of a particular fungible asset. In uses of this type, the type of asset should be implicit.

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

#### Choosing scales

The native unit or scale of the settlement engine is RECOMMENDED to be the same unit its settlements are denominated in, which is typically the smallest denomination of the asset on the settlement system.

The accounting system and settlement engine are RECOMMENDED to use the same unit or scale to minimize conversion inconsistencies.

#### Scale conversions

If the accounting system or settlement engine receives a request with a **[`Quantity`](#quantity-type)** denominated in a unit more precise than its unit, it MUST convert the quantity into its native unit. If so, the resulting amount MUST be rounded down before fulfilling the request.

The response to the request MUST include the converted, rounded **[`Quantity`](#quantity-type)** used to fulfill the request, which MUST be less than or equal to the amount sent in the original request.

Then, the system with the additional precision initiating the request MUST track the sum leftover by subtracting the two the other so it may accumulate and be added to the amount in subsequent requests.

### Settlement Engine HTTP API

#### Initiate an account

Inform the settlement engine that a new accounting relationship was instantiated. The settlement engine MAY perform tasks as prerequisite to settle the new account. For example, a settlement engine implementation might send messages to the peer to exchange ledger identifiers or to negotiate terms of the settlement arrangement.

The transport MUST be the only entity invoking this instruction to ensure the account identifier can be correlated with the correct peer to send and receive messages. Note that the transport also MUST have a mechanism to notify the accounting system that a new account should be instantiated (out-of-scope of this specification).

##### Request

```http
POST /accounts/:id HTTP/1.1
```

##### Response

```http
HTTP/1.1 201 CREATED
```

#### Perform outgoing settlement

Reconcile a liability owed to the peer for the given amount.

Note that the settlement engine MAY accrue owed settlements without settling immediately due to varying arrangements, implementations, or conditions. The settlement engine SHOULD persist amounts owed to the peer that have yet to be settled so they can be settled later.

The accounting system MUST be the only entity invoking this instruction and MUST preemptively debit this amount from the accounts payable, or some liability account tracking a balance owed to the peer, to ensure accurate accounting.

##### Request

```http
POST /accounts/:id/settle HTTP/1.1
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
POST /accounts/:id/handleMessage HTTP/1.1
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

TODO Rename to "Settlement engine callback API" ?

### Accounting System HTTP API

#### Credit incoming settlement

Notify the accounting system of receipt of an incoming settlement. Note that the settlement engine MAY accrue incoming settlement acknowledgements without immediately informing the accounting system.

The settlement engine MUST be the only entity invoking this message and MUST credit this amount to the accounts receivable, or some asset account tracking the balance owed by the peer, to ensure accurate accounting.

TODO "to properly reconcile the settlement"

##### Request

```http
POST /accounts/:id/receipt HTTP/1.1
Accept: application/json
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** that should be credited to the account as an incoming settlement

##### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** credited to the account
>
> - The amount credited MUST always be less than or equal to the quantity in the original request.
> - If the quantity credited is less than the quantity of the original request, the settlement engine MUST track the leftover amount so it may accumulate and be added to subsequent notifications to prevent the two systems getting out-of-sync.

### Transport HTTP API

#### Send outgoing request

Send a message to given peer's settlement engine and return its response. The settlement engine MUST be the only entity invoking this instruction.

##### Request

```http
POST /accounts/:id/sendMessage HTTP/1.1
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

_(The following section was adapted from the [Stripe API documentation](https://stripe.com/docs/api/idempotent_requests).)_

Each API MUST support [idempotency](https://en.wikipedia.org/wiki/Idempotence) for safely retrying requests without accidentally performing the same operation twice. This is useful when an API call is disrupted in transit and you do not receive a response. For example, if a request to send a settlement does not respond due to a network connection error, you can retry the request with the same idempotency key to guarantee that no more than one charge is created.

To perform an idempotent request, provide an additional `Idempotency-Key: <key>` header to the request.

Idempotency works by saving the resulting status code and body of the first request made for any given idempotency key, regardless of whether it succeeded or failed.

Subsequent requests with the same key return the same result, including `500` errors.

An idempotency key is a unique value generated by the client which the server uses to recognize subsequent retries of the same request. How you create unique keys is up to you, but we suggest using V4 UUIDs, or another random string with enough entropy to avoid collisions.

Keys expire after 24 hours, so a new request is generated if a key is reused outside of that time frame. The idempotency layer compares incoming parameters to those of the original request and errors unless they're the same to prevent accidental misuse.

Results are only saved if an API endpoint started executing. If incoming parameters failed validation, or the request conflicted with another that was executing concurrently, no idempotent result is saved because no API endpoint began execution. It is safe to retry these requests.

All `POST` requests accept idempotency keys. Sending idempotency keys in `GET` and `DELETE` requests has no effect and should be avoided, as these requests are idempotent by definition.

## Example Implementations & Arrangements

### Simple value transfers

Suppose two peers, Alice and Bob, are operating the same or compatible settlement engine implementations, which settle using a ledger which both Alice and Bob maintain accounts on.

1. Alice's accounting system instructs her settlement engine to perform a settlement of 5 units to Bob.
2. Subsequently, Alice's settlement engine sends a value transfer of 5 units from Alice's ledger account to Bob's ledger account.
   - To know where to send the payment, Alice may have configured her settlement engine with Bob's ledger identifier, or the settlement engine may automatically send a message to Bob's settlement engine to request Bob's ledger identifier.
   - The settlement engine implementation MUST ensure that an incoming payment is only credited to the peer's account that sent it.
3. Bob's settlement engine, always watching the ledger, recognizes the payment, correlates that Alice sent it, and notifies its accounting system of the incoming settlement for 5 units.

### Payment channels

Payment channels are special bilateral or multilateral settlement systems backed by escrows on an underlying shared ledger. They enable peers to adjust the allocation of these escrows among themselves. A participant can sign claims—messages with digital signatures entitling its peer to some greater portion of the escrow—which the peer can validate immediately without informing the underlying ledger. When the peers are done transacting, the most recent of many such claims is enforceable by the underlying ledger so the escrowed funds can be released and distributed accordingly.

Payment channels offer very fast and cheap settlement, which is beneficial to peers which don't extend much credit to one another.

Suppose two peers, Alice and Bob, are operating the same or compatible settlement engine implementations, which settle using a payment channel on a shared ledger.

1. Alice instructs her settlement engine to create a payment channel to Bob and fund it for 20 units.
   - Alice's settlement engine should escrow 20 units in the payment channel and inform Bob's settlement engine that a payment channel was created.
   - Note, however, that the funds are still in Alice's custody, and are still only accessible by Alice.
2. Alice's accounting system instructs her settlement engine to settle 5 units to Bob.
3. Alice's settlement engine signs a claim entitling Bob to 5 units from Alice's escrowed funds, and sends it to Bob's settlement engine.
   - If Bob already had some claim, the new claim should entitle Bob to 5 _additional_ units.
   - If Alice has already entitled Bob to all the available escrowed funds, the settlement engine may track that it owes Bob 5 units without sending a claim, until there's sufficient capacity in the payment channel.
4. Bob's settlement engine, upon receiving the claim, should verify the message is valid and its digital signature is authentic, and determine how much additional funds it's entitled to (in this case, 5 units). Then, it should it notify the accounting system that it received the given amount, 5 units.
5. Alice and Bob may repeat this process many times, as long as the party sending the payment channel claim has funds that haven't already been allocated to the peer. If additional funds need to be escrowed, the settlement engine may offer this functionality through a custom instruction.
6. At a later time, Alice or Bob may instruct their settlement engines to close the payment channel and release the allotted funds back to their respective ledger accounts.
   - Depending upon the payment channel implementation, there may be both cooperative and non-cooperative mechanisms for this, with varying time delays until the funds can be dispersed.
   - Settlement engines using payment channels may also have functionality to watch the underlying ledger to ensure the peer doesn't try to submit an old message that would incorrectly distribute the escrowed funds.

### Recipient collects a fee

Suppose Alice and Bob's settlement arrangement is such that, before Bob can begin acknowledging incoming settlements from Alice, Bob must collect some initiation fee related to the settlement system.

1. Alice sends a custom instruction to her settlement engine to settle the fee. Note that she does not use the instruction reserved for the accounting system.
2. Alice's settlement engine automatically negotiates the fee with Bob's settlement engine (likely subject to some limit).
3. Alice's settlement engine sends a payment on the shared ledger or system to Bob's settlement engine for the value of the fee.
4. Bob's settlement engine, instead of informing the accounting system of the incoming settlement, does nothing, but internally tracks that the negotiated fee was paid.
5. If Alice's accounting system triggers any subsequent settlements to Bob, Bob's settlement engine should acknowledge them to the accounting system as normal.

### Sender collects a fee

Suppose Alice and Bob's settlement arrangement is such that, in order for Alice to settle her liabilities to Bob, Alice requires that first Bob must pay a fee.

1. The settlement engine implementations that Alice and Bob are operating might negotiate the fee that Alice will collect (suppose a fee of 3 units).
   - The configuration of the settlement engines could ensure the fee is reasonable, or Bob could instruct his settlement engine of some limit for the fee.
2. After it's negotiated, Bob's settlement engine preemptively acknowledges it received an incoming settlement for 3 units.
   - Note that even though no settlement on the shared ledger or system was received, Alice and Bob did mutually agree to reconcile a future liability: that is, the fee charged to Bob by Alice.
3. As Alice and Bob transact with one another, the liabilities that Alice owes Bob accrue, and Alice's accounting system instructs her settlement engine to settle them.
4. Alice's settlement engine, instead of sending a settlement on the shared settlement system, should track the amount owed to Bob, until it accrues to 3 units, the value of the agreed fee.
5. After the value of the fee is accounted for through accrued settlements, if Alice's accounting system instructs her settlement engine to settle, it should send these additional settlements on the shared system or ledger.
   - For example, after negotiating the fee, suppose Alice's accounting system tells her settlement engine to settle 2 units. Nothing should happen, since it's accruing owed balance to cover the fee of 3 units.
   - If the settlement engine is later instructed to settle another 2 units, it should send a payment on the shared settlement system for 1 unit, since the other unit was taken out as apart of the fee.
   - Any further instructions to settle should trigger payments on the shared system as normal.
