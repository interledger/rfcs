---
title: Connector Risk Mitigations
draft: 1
---
# Connector Risk Mitigations

Interledger connectors take some risk in exchange for the revenue they generate from facilitating payments. This document outlines the major categories of risks connectors face and suggests some possible mitigations.

This is a work in progress and is not an exhaustive list.

**Monitoring is a must! Even connectors that implement all of these strategies should monitor their transaction patterns and use warnings or kill switches to avoid losing money in the case of an unexpected attack.**

## Fulfillment Failure

The main risk connectors face in Interledger is being unable to fulfill the incoming transfer after their outgoing transfer has been executed.

Possible mitigations include:

* **Connecting Reliable Ledgers** - Connectors should choose the ledgers they connect in part based on the reliability and speed of fulfillment notifications and the time the ledgers require to process fulfillments once they are submitted
* **Adjusting Transfer Expiry Window** - Connectors determine the window of time they require between when the incoming and outgoing transfers expire. Connectors should set this window such that they are confident that they will be able to deliver the fulfillment in time even if the outgoing transfer is executed at the last possible moment.
* **Denial of Service Protections** - Connectors should take standard [Denial of Service](https://en.bitcoin.it/wiki/Weaknesses#Denial_of_Service_.28DoS.29_attacks) attack prevention steps to prevent attackers from overloading the connectors' servers with network traffic
* **Prioritizing Fulfillments** - Connectors should prioritize fulfilling transfers over preparing new ones or responding to quote requests and may even have separate processes or machines responsible for those different behaviors
* **Redundant Instances** - Connectors should run redundant processes and machines to increase the difficulty of interfering with their processing
* **Avoiding Public Endpoints** - Connectors may reduce attack vectors by using communication channels and protocols that do not entail having a publicly-accessible server (for example using [WebRTC](https://webrtc.org/) or [Virtual Private Networks](https://en.wikipedia.org/wiki/Virtual_private_network) to communicate with peers

## Liquidity Exhaustion

Attackers could tie up connectors' liquidity by preparing payments through them that the attacker knows will fail. For example, an attacker could prepare numerous payments to itself and then not fulfill any of them.

Possible mitigations include:

* **Managing "Payment Bandwidth"** - Connectors should monitor the percentage of their total liquidity that is on hold at any given time for a given peer, customer, or destination prefix and may reject incoming payment requests if that party exceeds their allocated "payment bandwidth". Connectors may allocate less bandwidth to unknown or untrustworthy senders or receivers. Note that ILP Packets contain the destination account but not the source account, so connectors should apply this logic to the immediate peer or customer that they receive the payments from and possibly the destination account or prefix.
* **Preferring Smaller Payments** - Smaller payments place a smaller percentage of the connector's liquidity on hold and thus each one carries less risk that the payment being prepared and then failing would create significant opportunity cost
* **Blacklisting Senders and Receivers** - Connectors may refuse to facilitate payments from certain sources or to certain destinations if their rate of failed payments is unusually high

## Exchange Rate Volatility

Once connectors prepare their outgoing transfers, they are committed to the payment even if the exchange rate between the assets fluctuates.

Possible approaches include:

* **Accounting for Slippage** - Connectors may add a buffer to their expected exchange rate to account for some movement in the price, and they may add a premium for especially volatile currencies
* **Preferring Shorter Timeouts** - Connectors may provide better exchange rates for payments with shorter timeouts because they carry less risk that the price will move drastically while the payment is in flight

