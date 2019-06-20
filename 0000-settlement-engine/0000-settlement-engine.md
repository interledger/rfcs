---
title: Settlement Engine
draft: 1
---

# Settlement Engine

## Conventions

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://tools.ietf.org/html/rfc2119).

## Definitions

**Peers** are two participants that share an accounting relationship and have a medium to communicate with one another.

A **transport** is a communication layer for two peers to send messages between one another.

An **account** is a record of accrued obligations between two peers as they transact with one another, denominated in a particular fungible asset.

An **accounting system** tracks a participant's accounts and the net balance owed between peers.

A **settlement** is a reconciliation of a liability.

A **settlement system** is a medium for exchanging value.

## Overview

This specification codifies a **settlement engine**, a common interface between an accounting system and heterogeneous settlement systems.

Compatible settlement engine implementations enable peers to mutually reconcile one's liabilities through integrating with a shared settlement system.

The purpose of a settlement engine is to perform two primary operations:

1. Execute outgoing settlements to a peer
2. Acknowledge incoming settlements from a peer

Settlements may differ depending on the settlement engine implementation, such as transferring value on the underlying system or ledger, and/or using a custom protocol through which the peers mutually agree to reconcile a liability.

The core test case for a settlement engine implementation is **the sum of amounts an instance is instructed to settle should eventually equal the sum of amounts the peer's instance acknowledges receipt of.**

Varying implementations, arrangements, and conditions (such as connectivity to the ledger) may delay consistency of instructed and acknowledged settlements by an indeterminate amount of time.

## Example Settlement Arrangements

### Simple value transfers

Suppose two peers, Alice and Bob, are operating the same or compatible settlement engine implementations, which settle using a ledger which both Alice and Bob maintain accounts on.

1. Alice's accounting system instructs her settlement engine to perform a settlement of 5 units to Bob.
2. Subsequently, Alice's settlement engine sends a value transfer of 5 units from Alice's ledger account to Bob's ledger account.
   - To know where to send the payment, Alice may have configured her settlement engine with Bob's ledger identifier, or the settlement engine may automatically send a message to Bob's settlement engine to request Bob's ledger identifier.
   - The settlement engine implementation should ensure that an incoming payment is only credited to the peer's account that sent it.
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

### Sender collects a fee

Suppose Alice and Bob's settlement arrangement is such that, in order the Alice to settle her liabilities to Bob, Alice requires that first Bob must pay a fee.

1. The settlement engine implementations that Alice and Bob are operating might negotiate the fee that Alice will collect (suppose a fee of 3 units).
   - The configuration of the settlement engines could ensure the fee is reasonable, or Bob could instruct his settlement engine of some limit for the fee.
2. After it's negotiated, Bob's settlement engine preemptively acknowledges it received an incoming settlement for 3 units.
   - Note that even though no settlement on the shared ledger or system was received, Alice and Bob did mutually agree to reconcile a future liability: that is, the fee charged by Alice on Bob's behalf.
3. As Alice and Bob transact with one another, the liabilities that Alice owes Bob accrue, and Alice's accounting system instructs her settlement engine to settle them.
4. Alice's settlement engine, instead of sending a settlement on the shared settlement system, should track the amount owed to Bob, until it accrues to 3 units, the value of the agreed fee.
5. After the value of the fee is accounted for through accrued settlements, if Alice's accounting system instructs her settlement engine to settle, it should send these additional settlements on the shared system or ledger.
   - For example, after negotiating the fee, suppose Alice's accounting system tells her settlement engine to settle 2 units. Nothing should happen, since it's accruing owed balance to cover the fee of 3 units.
   - If the settlement engine is later instructed to settle another 2 units, it should send a payment on the shared settlement system for 1 unit, since the other unit was taken out as apart of the fee.
   - Any further instructions to settle should trigger payments on the shared system as normal.

### Recipient collects a fee

Suppose Alice and Bob's settlement arrangement is such that, before Bob can begin acknowledging incoming settlements from Alice, Bob must collect some initiation fee related to the settlement system.

1. Alice sends a custom instruction to her settlement engine to settle the fee. Note that she does not use the instruction reserved for the accounting system.
2. Alice's settlement engine automatically negotiates the fee with Bob's settlement engine (likely subject to some limit).
3. Alice's settlement engine sends a payment on the shared ledger or system to Bob's settlement engine for the value of the fee.
4. Bob's settlement engine, instead of informing the accounting system of the incoming settlement, does nothing, but internally tracks that the negotiated fee was paid.
5. If Alice's accounting system triggers any subsequent settlements to Bob, Bob's settlement engine should acknowledge them to the accounting system as normal.

## Specification

Operating a settlement engine requires three components each exposing a particular HTTP API: a settlement engine, an accounting system, and a transport.

API endpoints exposed by these systems may be classified in two ways:

1. Endpoints that may be invoked by one of these other two components, and MUST NOT be invoked manually. At a minimum, all settlement engine implementations MUST support these endpoints.
2. Endpoints that may be invoked manually by an operator.

This document outlines the first class of endpoints: those only essential to automated interoperability between these systems, and not manual operation.

### Accounts and identifiers

Each account MUST be identified by a unique, URL-safe string.

#### Accounts vs ledger identities

The settlement engine is RECOMMENDED to be responsible for correlating an account identifier to the peer's identity on the shared ledger or settlement system, if required.

For separation of concerns between the accounting system and the settlement system, the accounting system is NOT RECOMMENDED to have knowledge of the peer's identity on the shared settlement system, but rather only the account identifier described here.

#### Multiple accounts

Settlement engine implementations SHOULD support settling with multiple accounts.

#### Correlating messages

The transport MUST correlate incoming messages from the peer to the correct account identifier, and MUST correlate outgoing messages from an account identifier to the correct peer to send them to.

### Units and quantities

#### `Quantity` type

A quantity represents an amount denominated in some unit of a particular fungible asset. In uses of this type, the asset should be implicit.

##### Attributes

- **`amount`** string
  - Number of the given unit of the asset between 0 and the maximum 64-bit unsigned integer, 18,446,744,073,709,551,615 (inclusive).
  - The amount is encoded as a string to ensure no precision is lost on platforms that don't natively support full precision 64-bit integers.
- **`scale`** number
  - Number of orders of magnitude smaller this unit is as compared to the unit of exchange for the asset.
  - All units MUST be at least as precise as the unit of exchange. For example, if the asset is U.S. dollars, quantities cannot be denominated in $100 bills, since that's less precise than quantities denominated in multiples of $1. Thus, the scale MUST NOT be a negative integer.

##### Example

To represent $2.54 in units of cents, where the amount is multiple of $0.01:

```json
{
  "amount": "254",
  "scale": 2
}
```

#### Choosing scales

The unit or scale used for quantities by the settlement engine is RECOMMENDED to be the smallest denomination of the asset on the settlement system.

The accounting system and settlement engine are RECOMMENDED to use the same unit or scale.

#### Scale conversions

Since the systems MAY use different scales, when interfacing with one another, care must be taken to ensure the system with additional precision tracks the amount leftover by the other system so it may accumulate and eventually be correctly accounted for.

If one of the systems receives a request with a **[`Quantity`](#quantity-type)** denominated in a unit more precise than its unit, it SHOULD convert the quantity into its native unit. If so, the resulting amount MUST be rounded down before fulfilling the request.

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
> - If the amount is `0`, the settlement engine MAY retry failed or queued settlements.

##### Response

```http
HTTP/1.1 200 OK
Content-Type: application/json
```

> **[`Quantity`](#quantity-type)** enqueued to settle
>
> - This response does not guarantee that a settlement was executed.
> - If the settlement engine uses a unit less precise than the accounting system's unit, in order to prevent the two systems getting out-of-sync, it must indicate the amount it queued so the accounting system can correctly track the amount leftover.

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

### Accounting System HTTP API

#### Credit incoming settlement

Notify the accounting system of receipt of an incoming settlement. Note that the settlement engine MAY accrue incoming settlement acknowledgements without immediately informing the accounting system.

The settlement engine MUST be the only entity invoking this message and MUST credit this amount to the accounts receivable, or some asset account tracking the balance owed by the peer, to ensure accurate accounting.

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
> - If the accounting system uses a unit less precise than the settlement engine's unit in order to prevent the two systems getting out-of-sync, it must indicate the amount it acknowledged receipt of so the settlement engine can track the amount leftover.

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

## Usage in Interledger

Peers using the [Interledger protocol](https://github.com/interledger/rfcs/tree/master/0001-interledger-architecture) clear and fulfill conditional IOUs which affect their mutual accounting relationship.

Since Interledger merely provides a credit network, a peer's liabilities may accrue to the point at which they must reconcile them. Settlement engines provide a mechanism for peers in Interledger to settle their liabilities and continue transacting.

An Interledger connector MAY operate the accounting system and transport system that interfaces with the settlement engine.

### Motivation

The [Ledger Plugin Interface (LPIv2)](https://github.com/interledger/rfcs/blob/master/0024-ledger-plugin-interface-2/0024-ledger-plugin-interface-2.md) was originally designed as an abstraction for ledger integrations using Interledger. However, it introduced several problems:

1. Multi-account plugins must include logic for handling ILP packets, increasing implementation complexity.
2. Plugins bundle settlement and bilateral communication functionality, limiting composability with other transports.
3. The JavaScript specific interface prevents connector implementations in other programming languages from using existing plugins.
4. Plugins operate in the same process as the connector, which limits scaling the two systems independently.

This specification aims to provide an abstraction that rectifies these issues.
