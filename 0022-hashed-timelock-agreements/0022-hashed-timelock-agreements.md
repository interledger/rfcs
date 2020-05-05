---
title: Hashed-Timelock Agreements (HTLAs)
type: working-draft
draft: 2
---

# Hashed-Timelock Agreements (HTLAs)
> Generalization of [Hashed-Timelock Contracts (HTLCs)](#background-on-hashed-timelock-contracts-htlcs) used to secure Interledger payments.

_This document assumes some familiarity with HTLCs and Interledger. It briefly summarizes both but it may be best read after [IL-RFC 1: Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md)._

Interledger provides secure multi-hop payments using conditional transfers. Some ledgers natively provide conditional transfers using Hashed-Timelock Contracts (HTLCs). However, not all ledgers support HTLCs.

Hashed-Timelock Agreements (HTLAs) are a generalization of HTLCs that can be implemented over any type of ledger, whether or not the ledger supports HTLCs. HTLAs work with public and private blockchains, centralized ledgers, payment channels, and even with cash or cases where there is no ledger. There is a spectrum of HTLA types that require varying levels of ledger functionality and bilateral trust. This document describes how HTLAs work and outlines the features and tradeoffs of the different options.

**Note: Interledger payments can securely cross multiple types of HTLAs at the same time. The selection of HTLA type is strictly a bilateral decision. The type of HTLA used does not affect the security of others in the path.** For details on this see [Interledger Across Diverse HTLAs](#interledger-across-diverse-htlas).

## Table of Contents

1. [Background on Hashed-Timelock Contracts (HTLCs)](#background-on-hashed-timelock-contracts-htlcs)
2. [Hashed-Timelock Agreements (HTLAs)](#hashed-timelock-agreements)
3. [HTLAs Without Ledger Support](#htlas-without-ledger-supoprt)
4. [Interledger Across Diverse HTLAs](#interledger-across-diverse-htlas)
5. [Spectrum of HTLA Types](#spectrum-of-htla-types)
   1. [Conditional Payment Channels (with HTLCs)](#conditional-payment-channels-with-htlcs)
   2. [On-Ledger Holds/Escrow (using HTLCs)](#on-ledger-holds-escrow-using-htlcs)
   3. [Simple Payment Channels](#simple-payment-channels)
   4. [Trustlines](#trustlines)
6. [Appendix: Additional HTLA Types](#appendix-additional-htla-types)

_____

## Background on Hashed-Timelock Contracts (HTLCs)

A [Hashed-Timelock Contract (HTLC)](https://en.bitcoin.it/wiki/Hashed_Timelock_Contracts) is a conditional transfer where the condition is enforced by the ledger. It is a concept from the Bitcoin community that is used in the [Lightning Network](https://lightning.network).

When the transfer is "prepared", the sender's funds are put on hold by the ledger, pending the fulfillment of a predefined condition. The condition is a hashlock, or the digest of a cryptographic hash function, such as SHA-256 in Lightning and Interledger. The "contract" stipulates that the recipient may claim the funds by presenting a valid preimage of the hash digest before a given timeout. After the timeout, the funds are automatically returned to the sender. This is the Hashed-Timelock Contract.

HTLCs are enforced by the ledger, so the parties transacting only need to trust the ledger to correctly execute the contract. However, this mechanism requires support from the ledger and only works with ledgers that implement hashlocks and timeouts.

Interledger is designed to work with all ledgers, so it must support both ledgers with and without support for hashlocks and timeouts.

## Hashed-Timelock Agreements (HTLAs)

A contract is a certain type of agreement that is enforced by a third party. Hashed-Timelock Agreements (HTLAs) generalize the idea of HTLCs to include agreements that are enforced by a ledger. The principle has been in use in Interledger since the project was started but the HTLA term was proposed more recently in [this thread on the Interledger mailing list](https://lists.w3.org/Archives/Public/public-interledger/2017Jun/0009.html).

HTLAs enable secure Interledger payments through all types of ledgers, including those that do not support conditional transfers.

## HTLAs Without Ledger Support

Two parties using an HTLA over a ledger that does not support hashlocks and timeouts could proceed in the following manner. The sender would send a message to the recipient telling them that they want to "prepare" a transfer with a given hashlock and timeout. The parties agree that if the recipient presents the preimage of the hash before the timeout, the transfer is executed and the sender owes the recipient the money. Debts are settled using simple transfers on the ledger.

In the case of a post-funded agreement, the sender can settle their debt with the recipient either for every payment, if their ledger is fast and has low fees, or once the total amount owed reaches the parties' trust/credit limit. In this case, the recipient must trust the sender to pay what they owe. The risk can be limited by capping how much the sender can send before they settle up.

For pre-funded agreements, the sender transfers either the amount of an individual payment or a bulk amount to the recipient. The recipient then deducts the amount of each "conditional transfer" executed from the pre-funded amount. In this case, the sender must trust the recipient not to steal the pre-funded amount, but this risk can obviously be limited by capping the pre-funded amount.

HTLAs thus work with ledgers that support hashlocks and timeouts (as HTLCs) and with ledgers that do not.

For more details on HTLAs without ledger support see the sections below on [Simple Payment Channels](#simple-payment-channels) and [Trustlines](#trustlines).

## Interledger Across Diverse HTLAs

A single Interledger payment can cross multiple different types of HTLAs. The Interledger Protocol ensures that the security of each HTLA is independent of the other HTLA types used in the path.

This is a critical point for understanding HTLAs and Interledger, so we will use an example flow to illustrate it.

### Example Payment Flow

In this rendition of the classic Alice to Bob payment, Alice has an account on a blockchain that implements HTLCs and Bob has an account with a bank that does not implement HTLCs:

```
        On-Ledger HTLC                 Payment Channel                  Trustline
Alice --(Blockchain A)--> Connector 1 --(Blockchain B)--> Connector 2 --(Bank C)--> Bob
```

Each `--(...)-->` represents a different type of HTLA, but all of them use the same hashlock.

The Interledger protocol flow (detailed below) ensures that each participant only needs to care about the HTLAs in which they are directly involved. Failure in a different part of the path -- or the selection of a seemingly unwise HTLA type -- does not affect any other agreements.

#### Interledger Protocol payment flow:

1. `Alice` and `Bob` agree on the hashlock `H`. The preimage `P` is only known to `Bob` (and to `Alice` in the case of [PSK](../0016-pre-shared-key/0016-pre-shared-key.md)).
2. `Alice` prepares the transfer to `Connector 1` by creating and funding an HTLC on `Blockchain A` with hashlock `H` (see [On-Ledger Holds/Escrow](#on-ledger-holds-escrow-using-htlcs)).
3. `Connector 1` prepares a transfer to `Connector 2` via their shared payment channel, also using hashlock `H` (see [Simple Payment Channels](#simple-payment-channels)).
4. `Connector 2` prepares a transfer to `Bob` on their shared trustline using Hashlock `H` (see [Trustlines](#trustlines)).
5. If `Bob` produces the preimage `P` before the transfer timeout, `Connector 2` will "pay" `Bob` by increasing his balance on their trustline.
6. If `Connector 2` sends `P` to `Connector 1` before their transfer times out, `Connector 1` will send a signed claim to pay `Connector 2`. (Note that whether or not `Connector 1` actually does this is irrelevant to the other parties in the path. `Connector 2` has already paid out to `Bob` and that cannot be undone. `Connector 1` can submit the preimage to `Blockchain A` and still refuse to give the claim to `Connector 2`. This is a known and manageable risk for `Connector 2` and no other parties are affected by it.)
7. If `Connector 1` submits `P` to `Blockchain A` before the timeout, the transfer will be executed and `Alice` will receive the proof `P` that `Bob` was paid. (Note again that whether the HTLC on `Blockchain A` is properly executed only matters to `Alice` and `Connector 1`. The properties of a ledger only matter to the parties holding accounts on that ledger.)

One way to think of this is that HTLAs abstract away what it means to "get paid". That is just an agreement between two parties and no one else cares how that is structured. All that matters is that each individual is happy with the agreements they're directly a part of. Since all of the hashlocks will be the same, either all of the transfers will happen or none of them will (barring the connector fulfillment failure).

For more details on the Interledger protocol suite and security, see [IL-RFC 1: Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md).

_Internet "hat tip": the importance of being able to integrate **any** type of network was demonstrated by [RFC 1149: A Standard for the Transmission of IP Datagrams on Avian Carriers](https://tools.ietf.org/html/rfc1149)._

## Spectrum of HTLA Types

The various types of HTLAs present a tradeoffs between complexity and risk. The more functionality a ledger provides, the less the users of that ledger need to trust one another.

|  | Conditional Payment Channels (with HTLCs) | On-Ledger Holds/Escrow (using HTLCs) | Simple Payment Channels | Trustlines |
|---|---|---|---|---|
| **Ledger Support Required** | High | High | Medium | Low |
| **Implementation Complexity** | High | Medium | Low | Low |
| **Bilateral Risk** | Low | Low | Medium | High |

### Conditional Payment Channels (with HTLCs)

* **Ledger Features Required:** Payment Channels with HTLC Updates
* **Non-Functional Ledger Requirements:** Fast*
* **Money at Risk:** None
* **Examples:** [Lightning-Style Channels](https://lightning.network)*

With conditional payment channels, participants set up the channel by depositing funds in a shared, temporary account on the ledger. When a conditional transfer is prepared, the sender sends the recipient a signed update to the channel that includes a hashlock and timeout. The recipient may redeem the transfer amount if and only if they can present the hash preimage before the timeout. If the sender and recipient agree that the preimage was delivered before the timeout, they can exchange signed statements with the newly agreed upon channel balance. If there is a dispute, the recipient can present the last claim and the hashlock preimage to the ledger and the ledger will determine whether the preimage is valid and was submitted before the timeout.

Using conditional payment channels, the sender and recipient can transact without any funds being at risk, because all disputes will be mediated by the ledger. This can be used as a mechanism to enable a greater volume of payments "through" a ledger than the ledger can natively support.

&ast; **Note on ledger speed:** Conditional payment channels may be most appropriate for fast ledgers, because the timeout of each transfer must account for the ledger's processing time. The recipient relies on the fact that they can redeem their funds even if there is a dispute with the sender by presenting their claims and the hashlock preimages to the ledger. However, there are numerous reasons for senders and connectors to want or require that Interledger payments execute or fail quickly (for example for retries and to reduce exchange rate risk). As a result, conditional payment channels may only work with Interledger if the ledger can process claims in a few seconds or less.

### On-Ledger Holds/Escrow (using HTLCs)

* **Ledger Features Required:** Transfers with HTLCs
* **Non-Functional Ledger Requirements:** Fast, Low Fees, High Throughput
* **Money at Risk:** None
* **Examples:** [Ethereum Escrow Contract](https://github.com/interledgerjs/ilp-plugin-ethereum), [XRP Escrow](https://ripple.com/build/transactions/#escrowcreate)

If a ledger provides support for HTLCs and is fast and inexpensive enough, participants can send all Interledger payments directly through the ledger. The sender prepares the conditional transfer by putting funds into a ledger-provided hold account pending a given hashlock and timeout. If the recipient presents the hash preimage before the timeout, the ledger executes the transfer and deposits the funds into the recipient's account automatically. If the timeout is reached, the ledger returns the funds to the sender.

Using ledger-provided conditional transfers enables parties to transact with no risk, but the ledger must be capable of processing a high volume of payments quickly and with low fees.

### Simple Payment Channels

* **Ledger Features Required:** Unconditional, Unidirectional Payment Channels
* **Non-Functional Ledger Requirements:** N/A
* **Money at Risk:** Total Prepared/Fulfilled Without Claims
* **Examples:** [Bitcoin CLTV Channels](https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki), [XRP PayChan](https://ripple.com/build/payment-channels-tutorial/)

Simple payment channels allow parties to send a greater volume of payments than the ledger can process itself. To set up a simple, unidirectional payment channel the sender puts funds into a temporary account on the ledger shared with the recipient. Funds can only be withdrawn from the ledger by presenting a claim signed by both parties that specifies the portion of the funds that will be transferred to the recipient and amount that will be returned to the sender. The sender effectively pays the recipient by sending signed claims to the recipient (not the ledger) that entitle the recipient to withdraw a greater portion of the channel's funds.

To use a simple payment channel in an HTLA, the sender "prepares" the conditional transfer simply by sending a message to the recipient (including the hashlock and timeout). If the recipient presents the hash preimage before the timeout, the sender sends a new signed claim to the recipient to cover the total amount of the transfers sent thus far.

The agreement between the sender and recipient dictates how disputes are handled, including cases in which the recipient thinks they submitted the preimage in time and the sender thinks otherwise. Both parties should enforce their own view of the timeout, rather than deferring to the other party.

In this post-funded model, the recipient must trust the sender for the total amount of the prepared or executed transfers that is not yet covered by payment channel claims. The recipient limits their risk by capping the amount of the transfers they are willing to accept from the sender without the corresponding claims. The risk could be flipped from the recipient to the sender by making the sender pre-fund each transfer by the claim along with the message to prepare the transfer. Pre-funding with simple payment channels is slightly more complex because the recipient needs to send another payment channel update back to the sender if the transfer is rolled back.

The functionality necessary for simple payment channels is present in nearly all major blockchains today, including Bitcoin (even without [SegWit](https://en.bitcoin.it/wiki/Segregated_Witness)), Ethereum, XRP, Zcash, and Chain.

### Trustlines

* **Ledger Features Required:** Transfers Between Accounts
* **Non-Functional Ledger Requirements:** N/A
* **Money at Risk:** Total Trustline Balance
* **Examples:** [`ilp-plugin-virtual`](https://github.com/interledgerjs/ilp-plugin-virtual)

When a ledger does not provide any support for Interledger, parties can still connect to the Interledger using trustlines. The sender prepares the transfer by sending the recipient a message including the hashlock and timeout. If the recipient produces the hash preimage before the timeout, the sender's debt is increased by the transfer amount. Like with simple payment channels, the participants must agree on how to solve disputes, including disagreements about whether a hash preimage was submitted in time. The sender can continue sending payments until they reach the maximum balance allowed by the recipient. At that point, the sender settles their balance by making a transfer on the ledger.

In this model, one of the parties must trust the other for the full outstanding balance of the trustline. This may be suitable in cases where the sender and recipient are friends or have a long-standing business relationship.

Notably, trustlines work over any type of "ledger" -- including cash! As long as there is a way to transfer funds between the sender and recipient, they can send Interledger payments and settle only when the trust limit is reached. If the payment flows in both directions are balanced, there may never even be a need to settle.

## Appendix: Additional HTLA Types

This appendix includes additional HTLA types that are possible but were not mentioned above either because they are less desirable or have yet to be implemented.

### Third Party Escrow

A third party escrow provider can be used if the ledger supports fast, inexpensive transfers but does not support holds and the sender and recipient do not trust one another. In this case, the sender prepares a transfer by sending the funds to the escrow provider, along with the hashlock and timeout. If the recipient submits the hashlock preimage before the timeout, the escrow provider transfers the funds to the recipient. If not, the escrow provider transfers the funds back.

It is preferable for ledgers to implement holds natively, but this HTLA type may be used in cases where that is not possible or not happening. Both the sender and recipient must trust the escrow provider for the full value of each transfer, either because of reputation or legal arrangement. If the sender and recipient do trust one another up to some limit, they can avoid the need for a third party by using Trustlines.

### Notarized Payment Channels

Disputes may arise in payment channel-based HTLAs because of disagreements over timeouts. Since there is no single source of truth as to whether the hashlock preimage was submitted in time, clock skew or network delays could cause the recipient to think the transfer should be executed while the sender thinks it expired.

To mitigate the risk of timeout disputes, the sender and recipient could agree to use a third party notary to act as the timekeeper. The sender prepares the transfer by submitting the details to the notary and the recipient (unless the notary also acts as a message broker). The recipient submits the preimage to the notary, who enforces the timeout. The notary signs a statement attesting to whether the preimage was recieved in time and gives the signed message to both the sender and recipient.

Third-party notaries could be used with simple or more complex payment channels. In the simple, unconditional type, the notary's decision is not used in the actual payment channel updates but the notary merely as the decision-maker in the agreement between the sender and recipient. In the more complex variety, the payment channels could be constructed such that the channel updates are conditional upon the signed statement from the notary. When using third-party notaries the sender and recipient must trust the notary not to be colluding with one of the parties and to not sign two conflicting statements.

### Third Party Payment Channels

Falling in-between the guarantees of Third Party Escrow and Notarized Payment Channels, a "Third Party Payment Channel" involves escrowing money in a payment channel and giving a third party authority to create claims. To set up the payment channel, the sender funds a temporary account on the ledger as in a Simple Payment Channel. However, the third party's key is authorized to create claims on the channel balance instead of using the sender's public key.

When the sender prepares a transfer, they send a message to the recipient including the hashlock and timeout. To execute the transfer, the recipient submits the preimage to the third party. If the third party gets the preimage before the timeout, they pay the recipient from the sender's funds by signing a new claim.

In this model, the recipient does not need to trust the sender at all. The recipient instead trusts the third party to honestly enforce the timeouts and sign claims when preimages are submitted in time. This means that the recipient only needs to trust the third party for the transfers that have been executed but are not yet covered by claims.

The sender has to trust the third party not to create a claim for more than they owe, which means they trust the third party for the payment channel's whole balance. However, unless the third party is colluding with the receiver, they have no incentive to pay out more than the sender owes.

