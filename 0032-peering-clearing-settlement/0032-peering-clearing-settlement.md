---
title: Peering, Clearing and Settling
draft: 3
---

# Peering, Clearing and Settling

The Interledger network is a graph of nodes (connectors) that have peered with one another by establishing a means of exchanging ILP packets and a means of paying one another for the successful forwarding and delivery of the packets.

Further details on the ILP Protocol can be found in the [specification](../0027-interledger-protocol-4/0027-interledger-protocol-4.md).

## Accounts and Balances

The edge between any two nodes (peers) is a communication link (for exchanging ILP packets and other data), and an account held between the peers (the Interledger account). The Interledger account has a balance denominated in a mutually agreed upon asset (e.g. USD) at an agreed upon scale (e.g. 2). The balance on the account is **the net total of the amounts on any packets "successfully" routed between the peers**.

The balance on the Interledger account can only change as a result of two events:
 1. The "successful" routing of an ILP packet between the two peers
 1. A payment made between the peers on the underlying payment network they have agreed to use to settle the Interledger account

_**NOTE:** In this context a packet is considered "successfully" routed if it is routed to the correct recipient, and they reply with a valid ILP Fulfill response which is routed back before the expiry on the packet._

This document provides further details on when these events occur and how they are handled by the peers. 

Because amounts are sent in a standard form (unsigned 64-bit integers) as part of the ILP Prepare packet headers, it is necessary to infer the currency/asset and scale of the amount from the context of the packet.

This is why the asset and scale are pre-configured for each Interledger account between peers. Peers that wish to exchange packets using different assets or scale need to establish separate accounts for each.

> **Example : Alice and Bob peer using Satoshis**

> - Alice and Bob are nodes on the network.  
> - They agree to peer and exchange ILP packets using the [Bilateral Transfer Protocol (BTP)](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md)
> - They also agree to denominate their Interledger account in Bitcoin (BTC) at a scale of 8 and settle using the Lightning network.

> In this scenario Alice and Bob exchange ILP packets, which they are either sending or forwarding on behalf of another peer, using the BTP protocol. Every ILP Prepare packet has an amount (represented as an unsigned 64-bit integer). Because of how they have agreed to setup their peering relationship a packet with an amount of 5 represents 0.00000005 BTC (5 satoshis).

Once peered, the two connectors both track the Interledger account balance and adjust it for every ILP Packet successfully routed between them. 

When a connector sends an ILP Prepare packet to a peer, and receives a valid ILP Fulfill response, before the expiry of the ILP Prepare, their balance with that peer **decreases**. 

When a connector receives an ILP Prepare packet and returns a valid ILP Fulfill response, before the expiry of the ILP Prepare, their balance with that peer **increases**.

One peer's balance should always be the additive inverse (negation) of the other peer's balance. I.e. If one peer has a balance of 10 the other peer should have a balance of -10.

In financial accounting terms this could be viewed as a revenue/expense account where credits to this account are balanced by a debit to a corresponding "Accounts Receivable" asset account and debits to this account are balanced by a credit to a corresponding "Accounts Payable" liability account.

> **Example : Understanding Alice and Bob's accounts**

> Assuming they start with a balance of 0 and the following sequence of events occurs:

> 1. Alice passes an ILP Prepare to Bob with an amount of 6.
> 2. Bob replies, before the request expires, with a valid ILP Fulfill.
>   - Alice's balance is now -6 satoshis
>   - Bob's balance is now 6 satoshis
> 3. Bob passes an ILP Prepare to Alice with an amount of 2.
> 4. Alice is unable to route the packet and replies with an ILP Reject.
>   - Alice's balance is still -6 satoshis
>   - Bob's balance is still 6 satoshis
> 5. Bob passes an ILP Prepare to Alice with an amount of 20.
> 6. Alice replies, before the request expires, with a valid ILP Fulfill.
>   - Alice's balance is now 14 satoshis
>   - Bob's balance is now -14 satoshis

## Clearing

The traditional definition of clearing a payment is the process by which the two parties establish their net positions and reconcile any differences.

In the Interledger case this would involve the two peers exchanging data on what their current balance is and, if there is a discrepency, resolving this.

Notably, clearing is not part of the Interledger standard, as the means by which two peers perform these operations is a bilateral concern (i.e. has no impact on others in the network).

Current implementations of ILP do not have a standardized clearing process, as most peers settle very frequently using networks on which this is possible such as distributed ledgers which support payment channels, reducing the risk of discrepencies developing in their account balances.

However, there is an edge case where the peer's balances may be out of sync, as demonstrated in this example:

> **Example : Alice and Bob reconcile**

> Assuming they start with a balance of 0 and the following sequence of events occurs:

> 1. Bob passes an ILP Prepare to Alice with an amount of 20.
> 1. Alice replies with a valid ILP Fulfill and believes she has done so before the request expires, however Bob considers the request to have expired and has already rejected the payment to his downstream peer.
>   - Alice's balance is 20 satoshis
>   - Bob's balance is 0 satoshis

> Clearly, Bob and Alice need to reconcile this situation however the specific mechanism they use and recourse they take to resolve this difference is outside the scope of the Interledger protocol.

It is important to note that this is an extremely unlikely scenario as telescoping expiry timeouts between peers should reduce the risk of this to almost zero.

_**NOTE:** Telescoping timeouts is the process of subtracting some time from the expiry on a packet before forwarding it. As a result the expiry time gets shorter at each hop. The amount that a node subtracts is at its discretion so it can ensure it gives itself enough time to pass the fulfillment back._

Further, this is a single packet, and a key principal of the Interledger network is to break payments into very small packets so that in the unlikely event that this does occur the losses incurred by the two parties are negligible.

Nonetheless, it is likely that future bilateral protocols (like BTP) will define more detailed processes for reconciliation and clearing.

## Settlement

It is unlikely that the flow of packets between two peers will always net out such that the balance continuously tends toward zero. In most cases flows will be predominantly in one direction and there will be a need for the peers to reduce (or raise) them back to 0.

This avoids a situation where one peer owes the other a large sum of money and is then unable or unwilling to pay (settlement risk). Connectors should define a maximum Interledger account balance to manage the settlement risk they expose themselves to with their peers.

Further, the predominant peering arrangement on the open Interledger network is to settle as often as is practically possible and financially viable such that this risk is very low.

In the case of peers that use payment channels to settle this can be done for every packet as the cost of settlement is almost zero (the cost of exchanging claims or updates on the channel). This reduces the settlement risk between peers down to the value of only those packets that are not yet fulfilled, rejected or expired (i.e. packets that are in-flight).

Connectors will configure their own business rules regarding when to settle, based on how much they trust their peers and the costs and speed of settlement on the underlying network.

For most implementations, this configuration will consist of, at a minimum, a maximum balance, and a settlement threshold. 

### Maximum Balance

When a connector receives an incoming packet from a peer it will ensure that the amount of the packet, added to the current balance, does not exceed the maximum balance. If it does it MUST reject he packet with a [T04 - Insufficient Liquidity](https://interledger.org/rfcs/0027-interledger-protocol-4/#error-codes) error.

This is only likely to occur if: 
 1. The settlement threshold is lower than the additive inverse (negation) of the maximum balance at the peer, or
 1. The sending peer is unable to settle the account fast enough to keep up with the total amount in the packets being sent.

In the former case the peer may choose to perform a settlement, even though it has not reached its settlement threshold so that the balance on the Interledger account at the peer is reduced below the maximum. 

In the latter case, the sending peer may need to throttle back on the packets it sends to the upstream peer or they will need to make an alternative settlement arrangement that can accomodate the volume.

### Settlement Threshold

When a connector receives a successful response from a peer it will evaluate if the amount of the packet, subtracted from the current balance, is less than the settlement threshold. If so, the connector should perform a settlement, following which the balance on the Interledger account is adjusted up by the settlement amount.

In a correctly configured peering the additive inverse (negation) of the settlement threshold of one peer will be less than the maximum balance of the other peer (see below for an example).

> **Example : Alice and Bob settle their account**

> Assuming they start with a balance of 0 and have configured the following. 

> - Alice has configured a settlement threshold of -10. This means Alice will settle with Bob as soon as she owes him 10 satoshis or more.
> - Alice has configured a maximum balance of 20. This means Alice will reject any packets from Bob that would move the balance higher than 20.
> - Bob has configured a settlement threshold of -15. This means Bob will settle with Alice as soon as he owes her 15 satoshis or more.
> - Bob has configured a maximum balance of 5. This means Bob will reject any packets from Alice that would move the balance higher than 5 satoshis.

> If the following sequence of events occurs:

> 1. Bob passes an ILP Prepare to Alice with an amount of 12.
> 1. Alice replies with a valid ILP Fulfill. Alice's balance is now 12. Bob's balance is -12.
> 1. Bob passes an ILP Prepare to Alice with an amount of 9.
> 1. Alice rejects this with a T04 error code because this would take her balance over 20.
> 1. Bob passes an ILP Prepare to Alice with an amount of 7.
> 1. Alice replies with a valid ILP Fulfill. Alice's balance is now 19. Bob's balance is -19.
> 1. Bob's balance is now past his settlement threshold of -15 so he makes a 19 satoshi Lightning payment to Alice and notifies her that he has settled the account. Bob's is now 0.
> 1. Alice receives the payment and adjusts her balance to 0.
> 1. Alice passes an ILP Prepare to Bob with an amount of 2.
> 1. Bob replies with a valid ILP Fulfill. Bob's balance is now 2. Alice's balance is -2.
> 1. Alice passes an ILP Prepare to Bob with an amount of 5.
> 1. Bob rejects this with a T04 error code because this would take his balance over 5.

> Note how, because Bob has used very conservative limits on his maximum balance, and Alice has used a larger number for her settlement threshold, a situation will regularly arise where Bob reject packets from Alice because she is going to exceed Bob's maximum balance but she never hits her settlement threshold. While Alice can overcome this by settling whenever Bob rejects a packet with a T04 error a better solution would be for Alice to configure her threshold to be within Bob's maximum balance.

### Settlement Models and Mechanisms

It should be clear at this point that the successful exchange of ILP packets between peers creates obligations between them that must be settled.

What may not be obvious is that these obligations may also be "pre-settled". The most common model in use today is for a peer to send a packet, wait for it to be successfully routed, and then settle the Interledger account immediately or some time after. This is the "post-paid" model and is also the most common model for payments, clearing and settlement in other networks.

However, nothing prevents two peers from creating a pre-paid settlement arrangement where the settlement must precede the ILP packet. This will most likely take place in an environment where the trust between peers is not shared equally (especially if a fast and cheap settlement mechanism is not available).

Rather than take on any settlement risk, one peer may insist that the other always maintain a positive Interledger account balance. In this case the [Maximum Balance](#maximum-balance) is configured by that peer to be 0.

It is important to note that this has no impact on the settlement models used by others that have peered with these two nodes. An ILP packet can traverse a number of peer links, all of which have different settlement models and configurations.

### Settlement vs Settlement

The term settlement can be heavily overloaded in a payments context so it is important to note that in this document we refer to settlement as the settling of the Interledger account between two peers.

If this is done using a payment over a network that has its own settlement phase, we still consider the act of paying the peer to be settlement.

> **Example : Alice and Bob settle (with each other)**

> Alice and Bob are settling in BTC using the Lightning network. In order to do this they both had to join the Lightning network and commit BTC to payment channels on that network.

> It could be argued that payments on the Lightning network are only settled once the channel is closed and all claims have been submitted on-chain. However, when settling the Interledger account between them, simply completing the Lightning payment is enough to consider the account settled as this is an irrevocable payment.
