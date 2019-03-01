# Interledger Ping Protocol

## Introduction

In order to monitor the health of an internetworked system, it is often useful to be able to send probe messages. In the Internet system, ICMP [echo](https://en.wikipedia.org/wiki/Ping_(networking_utility)#Echo_request) request and response packets are used together to verify connectivity (colloquially known as a "pinging" a host).  

This RFC specifies a similar mechanism for Interledger nodes to test `uptime` and fulfill/reject `response-time` for a particular payment path, from the perspective of a payment sender.

## Scope
It is already possible to test unidirectional, end-to-end connectivity in Interledger by sending a small payment using existing mechanisms. However, doing so requires higher-level protocols, such as [SPSP](https://github.com/interledger/rfcs/blob/master/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) and [STREAM](https://github.com/interledger/rfcs/blob/master/0029-stream/0029-stream.md).

Instead, this protocol uses only [Interledger-layer](https://github.com/interledger/rfcs/blob/master/0001-interledger-architecture/0001-interledger-architecture.md#interledger-protocol) technologies, plug a a known condition/fulfillment pair, thus allowing a sender to control the expected response type while at the same time preventing a sender from utilizing bandwidth without paying for it

The ping protocol is not designed to debug routing issues and does not provide additional diagnostic information about the state of routing. That use case would be better served by a separate `traceroute` mechanism.

Additionally, the ping protocol is not designed to test bi-directional connectivity. For example, when a node encounters a ping protocol request, it either fulfills or rejects the payment, but does not perform any kind of "mirror payment" in response. That use case would be better served by a separate `echo` mechanism. 

All Interledger implementations _SHOULD_ respond to ping protocol requests, unless a node has a specific reason not to, such as security or privacy concerns.

## Terminology

* The **Sender** is the Interledger node initiating the ping request.
* The **Recipient** is the Interledger node responding to the ping request.
* **Source amount** is the amount debited from the sender of an ILP payment.
* **Destination amount** is the amount credited to the recipient of an ILP payment.
* The **Known Preimage** is the [ASCII](https://tools.ietf.org/html/rfc20) string `pingpingpingpingpingpingpingping`, which in Base64 is `cGluZ3BpbmdwaW5ncGluZ3BpbmdwaW5ncGluZ3Bpbmc`. 
* The **Known Condition** is the SHA256 hash of the Known Preimage, which when encoded using Base64 is `jAC8DGFPZPfh4AtZpXuvXFe2oRmpDVSvSJg2oT+bx34=`*[]: 

## Protocol
1. Sender sends a Prepare packet using the following details:
   - Amount: Any amount chosen by the sender.
   - Condition: The Known Condition, as defined above.
   - Destination ILP address: Recipient's Interledger address.
   - Packet Data: Unspecified.
  
2. Upon receiving the Prepare packet, the Recipient _SHOULD fulfill the payment using the following information:
   - Fulfillment: The Known Fulfillment, as defined above.
   - Packet Data: Unspecified.

Note that a recipient _MAY_ reject the payment if appropriate, for example due to an insufficient amount, invalid expiry, or for other factors.

 
## Recommended Uses

* Interledger participants may use this mechanism to test their own connectivity by sending pings to one or more destinations that are known to support the protocol described in this document.

* A monitoring service that is testing the availability of different ILP addresses may also send pings to these destinations from various sources. Interledger nodes that wish to be listed in such a monitoring service must support the protocol described in this document.