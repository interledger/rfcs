# Interledger Ping Protocol

## Introduction
In order to monitor the health of an internetworked system, it is often useful to be able to send probe messages. In the Internet system, ICMP [echo](https://en.wikipedia.org/wiki/Ping_(networking_utility)#Echo_request) request and response packets are used together to verify connectivity (colloquially known as a "pinging" a host).  

This RFC specifies a similar mechanism for Interledger nodes to test `uptime`, `response-time` and approximate `path cost` for a particular sender/Receiver pair.

## Scope
It is already possible to test end-to-end connectivity in Interledger by sending a small payment using existing mechanisms. However, doing so requires higher-level protocols, such as [SPSP](https://github.com/interledger/rfcs/blob/master/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) and [STREAM](https://github.com/interledger/rfcs/blob/master/0029-stream/0029-stream.md).

Instead, this protocol uses only [Interledger-layer](https://github.com/interledger/rfcs/blob/master/0001-interledger-architecture/0001-interledger-architecture.md#interledger-protocol) technologies to test connectivity between two nodes in the Interledger.
 
This protocol is not designed to debug routing issues and does not provide additional diagnostic information about the state of routing. That use case would be better served by a separate `traceroute` mechanism.

All Interledger implementations _SHOULD_ respond to ping protocol requests, unless a node has a specific reason not to, such as security or privacy concerns.

## Terminology

* The **Initiator** is the Interledger node initiating the ping request.
* The **Recipient** is the Interledger node responding to the Initiator's request.
* **Source amount** is the amount debited from the sender of an ILP payment.
* **Destination amount** is the amount credited to the Recipient of an ILP payment.

## Overview
This RFC defines two ping protocol modes: unidirectional and bidirectional.

* **Unidirectional**: A ping Initiator sends a specially formed "ping" packet, and the Receiver either fulfills or rejects the packet according to the rules defined in [Unidirectional Mode](#Unidirectional Mode).

* **Bidirectional**: An Initiator sends a specially formed "ping" packet that prompts the Receiver to send an additional "pong" packet. Upon receiving this pong packet, the Initiator either fulfills or rejects according to the rules defined in [Bidirectional Mode](#Bidirectional Mode), thus prompting the Receiver to fulfill or reject the original ping packet.

The primary difference between the two modes is that unidirectional mode allows an Initiator to test connectivity from the Initiator to the Recipient only, whereas bidirectional mode allows the Initiator to test connectivity in both directions.

## Unidirectional Mode
This mode enables an initiator to test connectivity from itself to a recipient. This flow relies upon a known condition/fulfillment pair, as follows:

* The **Ping Protocol Fulfillment** is the [ASCII](https://tools.ietf.org/html/rfc20) string `pingpingpingpingpingpingpingping`, which is `0x70696E6770696E6770696E6770696E6770696E6770696E6770696E6770696E67` in hexadecimal encoding.

* The **Ping Protocol Condition** is the SHA256 hash of the Ping Protocol Fulfillment, which is `0x8c00bc0c614f64f7e1e00b59a57baf5c57b6a119a90d54af489836a13f9bc77e` in hexadecimal encoding. 

To execute this flow, participants perform the following steps:

![unidirectional-flow](images/unidirectional-flow.svg)

1. Initiator sends an ILP Prepare packet containing the following details:
   - **Destination**: Recipient's Interledger address.
   - **Amount**: Any amount chosen by the Initiator.
   - **Expiry**: Any appropriate expiry.
   - **Condition**: The Ping Protocol Condition, as defined above.
   
1. Upon receiving the Prepare packet, the Recipient MUST fulfill the payment using the following information:
   - **Fulfillment**: The Ping Protocol Fulfillment, as defined above.

Note that a Recipient _MAY_ reject the payment if appropriate, for example due to an insufficient amount, invalid expiry, or for other factors.

## Bidirectional Mode
This mode enables an initiator to test connectivity from itself to a receiver, as well as vice versa. To execute this flow, participants perform the following steps:

![bidirectional-flow](images/bidirectional-flow.svg)

1. Initiator generates a new random 32-byte value to use as a fulfilment (`F`) and computes the corresponding condition (`C`).
1. Initiator sends an ILP Prepare packet to the Recipient with the following details (1):
   - **Destination**: The Recipient's Interledger address.
   - **Amount**: Any amount chosen by the Initiator.
   - **Expiry**: An appropriate expiry that is long enough to allow for two round trips.
   - **Condition**: The condition `C`.
   - **Data**: A concatenated series of bytes with the following information:
      - the bytes of the ASCII string `ECHOECHOECHOECHO`. In hexadecimal this value is `0x4543484F4543484F4543484F4543484F`.
      - the byte `0x00`
      - The ILP address of the Initiator (i.e., the return address) as an [OER-encoded](https://github.com/interledger/rfcs/blob/master/0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md), variable length IA5 string.
1. Upon receiving the Prepare packet, the Recipient identifies that it is a bidirectional Ping request by confirming the following:
    1. The packet is addressed directly to itself. For example, a node with the address `example.node1` would only respond to ping packets addressed to that specific address, but would not respond packets  addressed to `example.node1.child`.
    1. The packet has a payload conforming to the specification above (e.g., the byte following the `ECHOECHOECHOECHO` prefix in the payload is `0x00`).
1. The Recipient SHOULD NOT immediately send an ILP fulfill response. Instead the Recipient sends a new ILP prepare packet addressed to the address parsed from the original original packet's payload (2). This new packet has following details: 
    - *Destination*: The Interledger address found in the original packet's data payload.
    - *Amount*: The appropriate amount as chosen by the routing and FX logic of the Connector.
    - *Expiry*: An expiry that is marginally smaller than the expiry on the original ILP Prepare.
    - *Condition*: The same condition `C`.
    - *Data*: A concatenated series of bytes with the following information:
      - the bytes of the ASCII string `ECHOECHOECHOECHO` (`0x4543484F4543484F4543484F4543484F` in hexadecimal).
      - the byte `0x01`
1. Upon receiving this packet, the Initiator identifies that it is a Pong by the fact that it is addressed to the address used in the original Ping request.
1. The Initiator fulfills this second packet using the fulfilment `F` (3).
1. Upon receiving the ILP `Fulfill` packet from the Initiator, the Recipient then fulfills the original Ping request using the same fulfillment `F`.
1. The initiator finally receives the `Fulfill` packet (4).

## Implementation Considerations
1. Initiators SHOULD construct ping packets with amounts that are as small as possible in order to minimize any aggregate costs due to ping traffic.

1. Information obtained from this protocol (e.g., response times, route costing, node uptime, etc) is generally NOT authenticated, and SHOULD be used with caution, taking into account the route a particular ping packet traverses, if possible. 

    For example, it's possible that an intermediary node could detect a ping protocol flow and forge a seemingly valid fulfill or reject response. This type of activity might, for example, make it appear that response times are better than normal, or that a ping destination is fulfilling or rejecting when the opposite might be true.

### Bidirectional Mode Considerations
1. When assembling a return address in a "ping" packet, Bidirectional-mode Initiators SHOULD append a unique suffix to their own address so that each particular pinging session will use a unique return address. This will significantly decrease the odds of fraudulent "pong" requests in this mode.

1. Bidirectional-mode Initiators control the destination of all "pong" packets, so the Recipient of any "ping" packets in this mode SHOULD be careful to guard against accidental denial-of-service (DOS) attacks whereby an attacker utilizes the ping Recipient to send large volumes of pong traffic to a target ILP address of the Initiator's choosing.

1. When constructing a bidirectional "pong" response, it is important that implementations do not hard-code the amount or the outgoing link. Instead, implementations SHOULD process the response packet through the typical pipeline logic of the Connector. This will simplify implementations and also guard against subtle exchange rate attacks that might be attempted by an Initiator.
