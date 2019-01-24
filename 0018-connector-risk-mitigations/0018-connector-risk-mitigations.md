---
title: Connector Risk Mitigations
draft: 3
---
# Connector Risk Mitigations

Interledger connectors take some risk in exchange for the revenue they generate from facilitating payments. There are also scenarios in which connectors will facilitate payments without taking margin and need to account for greater risk. This document outlines the major categories of risks connectors face and suggests some possible mitigations. This is a work in progress and is not an exhaustive list.

**Monitoring is a must! Even connectors that implement all of these strategies should monitor their transaction patterns and use warnings or kill switches to avoid losing money in the case of an unexpected attack.**

## Fulfillment Failure

The main risk connectors face in Interledger is being unable to fulfill the incoming transfer after their outgoing transfer has been executed.

Possible mitigations include:

* **Adjusting Transfer Expiry Window** - Connectors determine the window of expiration for a transfer (within a full prepare-fulfill payment cycle) during the prepare phase. The expiration is dependent on the amount of time it takes for a connector to receive a fulfill from from their bilateral party. Forwarding connectors should set the window such that they will be able to receive the fulfillment and deliver it to the previous connector in time even if the outgoing transfer is executed at the last possible moment.
* **Denial of Service Protections** - Connectors should take standard [Denial of Service](https://en.bitcoin.it/wiki/Weaknesses#Denial_of_Service_.28DoS.29_attacks) attack prevention steps to prevent attackers from overloading the connectors' servers with network traffic. This includes IP-level protections and ILP-level protections.
* **Prioritizing Fulfillments** - Connectors should prioritize fulfilling transfers over preparing new ones and may even have separate processes or machines responsible for those different behaviors.
* **Redundant Instances** - Connectors should run redundant processes and machines to increase the difficulty of interfering with their processing.
* **Avoiding Public Endpoints** - Connectors may reduce attack vectors by using communication channels and protocols that do not entail having a publicly-accessible server (for example using [WebRTC](https://webrtc.org/) or [Virtual Private Networks](https://en.wikipedia.org/wiki/Virtual_private_network) to communicate with peers.

Note that unconditional payment channels do not require longer timeouts while enabling peers to rebalance frequently and minimize their bilateral trust.

## Payments Griefing

Liquidity Exhaustion: Attackers could tie up connectors' liquidity by preparing payments through them that the attacker knows will fail. For example, an attacker could prepare numerous payments to itself and then not fulfill any of them.

Possible mitigations include:

* **Managing "Payment Bandwidth"** - Connectors should monitor the percentage of their total liquidity that is on hold at any given time for a given peer, customer, or destination prefix and may reject incoming payment requests if that party exceeds their allocated "payment bandwidth". Connectors may allocate less bandwidth to unknown or untrustworthy senders or receivers. Note that ILP Packets contain the destination account but not the source account, so connectors should apply this logic to the immediate peer or customer that they receive the payments from and possibly the destination account or prefix.
* **Preferring Smaller Payments** - Smaller payments place a smaller percentage of the connector's liquidity on hold and thus each one carries less risk that the payment being prepared and then failing would create significant opportunity cost - in ILPv4, this is the default.
* **Blacklisting Senders and Receivers** - Connectors may refuse to facilitate payments from certain sources or to certain destinations if their rate of failed payments is unusually high.

Counterparty Theft: Since connectors forward packets on credit, they take a risk that the counterparty doesn't or can't settle later.

Example:
Suppose you have connectors A, B, C and D, and the payment is going from A->B->C->D. Take the case of C. During the fulfill phase, D will pass a fulfill packet to C, meaning that C will have to pay. It's important to note that the balances have been updated, but settlement can occur at a later time if dealing with a trusted counterparty. In the best case scenario, we settle in payment channels on every balance update. But because ILP is using unconditional payment channels for settlements, C can write a malicious client that could forward a fulfill packet to B, and avoid paying D by withholding settlement. In this case, A would pay B, B would pay C, but C didn't pay D.

Possible mitigations include:
* **Limiting total counterparty risk** - When forwarding packets for a peer,
    limiting the total value of unsettled payments is by leveraging pre-emptive
    payment channel updates after the fulfill phase limits the amount a
    counterparty could steal. If the settlement receiving in a payment channel
    is less than that of an on chain-fee, a connector that cheats its counterparty would lose much
    more capital in the process. For example, a connector that has been deprived of
    payment from its counterparty could refuse to facilitate future payments,
    and the malicious counterparty would have to close their payment channel to
    make the stolen micropayment amount liquid. Given that on-chain transaction fees
    are much higher than that of a micropayment in Interledger (i.e. 1 satoshi), an
    attacker would lose more money opening and closing channels to cheat their
    counterparty. Therefore, while this griefing attack is possible, if
    connectors are leveraging smaller payments and are requiring settlement down
    to the unit of a packet (ideally less than a on-chain fee),
    the attacking connector is more incentivized to facilitate payments to make
    profit on the exchange rate/fees.
* **Use an external arrangement** - Previously, we've mentioned that
    connectors are more likely to cooperate so they can earn margin on packet
    transfers. However, there are some scenarios in which they are not seeking a margin
    (i.e. a connector could have a model for charging its customers a flat rate for
    a certain amount of bandwidth at 0% margins). In these scenarios, it makes more
    sense for the connectors involved to leverage legal agreements (similar to what
    ISPs do for forwarding BGP packets) among connectors that are on-path and by KYCing
    any future counterparties that may want to forward packets to them.

## Solved Issues

These were risks that were present in older versions of the protocol and are
no longer the case.

### Exchange Rate Volatility

Once connectors prepare their outgoing transfers, they are committed to the payment even if the exchange rate between the assets fluctuates. The support of low-value packets allows for connectors to do exchange rates on a very fine-grained basis. Additionally, by having shorter timeouts for the prepare packets connectors are limiting their risk of being taken advantage from by the free option problem.

In the free option problem, a connector during the fulfill phase can receive a fulfill packet but decide whether or not proceed with payment when receiving the packet based on the current exchange rate of whole market. In the optimal case (for the payer), connectors receiving the fulfill packet can hold their payment until just before the expiry of the packet and then complete only if the exchange rate moved in the sender's favor.

### Unreliable Ledgers

In the Lightning Network and older versions of ILP, HTLCs (Hash-Timelock Contracts) are used for multi-hop payment channels. The pre-image condition that is agreed upon between sender and receiver is enforceable on chain, and allows for an interoperability method known as an atomic swap.

Unfortunately, HTLCs require timing assumptions as atomically locking up funds and settling on-chain involves locking up funds for time from when a transaction is sent until block finality. This means that if we have a payment from A->B->C, when C claims the money from B, the protocol must prevent race conditions in which A and B can pull out funds if C is not responsive. An example of a race condition would be where C claims the funds from B, but A tries to close its channel with B before B is able to claim funds from A. In order to get around this, atomic swaps between payment channels of connectors are secured under a synchrony assumption, in which the time it takes to submit a transaction to the main chain in case of unresponsive counterparty is heavily considered. We've previously suggested connectors choose the ledgers they plug-in based on the reliability and speed of fulfillment notifications and the time the ledgers require to process fulfillments once they are submitted, but this is no longer needed for risk mitigation because of simplified payment structure.
