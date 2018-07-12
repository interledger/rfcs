---
title: Interledger Node - Requirements Specification
draft: 1
---
# Interledger Node - Requirements Specification

An ILP node is a system that performs the necessary functions to route ILP packets between peers on the open Interledger network.

This document defines the basic functions of an ILP node. 

The document is specific to the requirements of a "core" node that only operates at the ILP layer and does not concern itself with functionality in the higher protocol layers (e.g. STREAM, PSK2, etc). In other words, this document describes the functions of a node that is neither a sender or receiver of ILP packets but rather a "middle-box", to borrow some Internet terminology.

An ILP node is also described as a connector. In this document, to emphasize that is is a node of the entire ILP network graph that routes ILP packets, it is written as an ILP node rather than a connector.

# Overview

An ILP node is very similar to a network router on an IP network. It has multiple incoming and outgoing links on which it sends and receives packets of data. It's primary function is to route incoming packets, on any links, to the appropriate outgoing link.

Where an ILP node differs from an IP router is that it MUST be stateful. ILP packets come in request/response pairs so a node that receives a request on one link, and then routes it out on another, MUST ensure it is able to match any response it gets back on the outgoing link to the original request sent on that link. It MUST also route the response back along the same incoming link on which it received the original incoming request.

The business logic of an ILP node is also more sophisticated than an IP router, in that the node operator is paid, per packet, by the sender of incoming packets to perform this function. It follows therefore, that the operator must also pay the next node for every packet it sends to it.

However, payment for forwarding a packet is only due if a **valid** response to a request is received **within a predefined expiry** therefor the node must also track the payments owed and due for accepting and forwarding packets, must reconcile the amounts owed to, and due from, peers and respond to (or initiate) external settlement events on those accounts.

# Key Concepts

## Interledger Packets

ILP packets are not unlike IP packets, in that they are a well-defined octet-based encoding for a payload of data, encapsulated in an envelope with a set of well-known headers. 

However, as ILP is a request/response protocol there are 3 packet types, not 1 as in IP. They are: 

- ILP Prepare (request)
- ILP Fulfill (success response), and
- ILP Reject (error response)

Packets use OER (Octet Encoding Rules) encoding and have the following headers:

### ILP Prepare
| Header             | Type        | Description                                                                                                   |
|--------------------|-------------|---------------------------------------------------------------------------------------------------------------|
| amount             | UInt64      | Amount offered to forward the packet. Currency and scale are implied by the link on which the packet is sent. |
| expiresAt          | Timestamp   | The time when the offer to pay to forward the packet expires.                                                 |
| executionCondition | UInt256     | A SHA-256 hash digest of the fulfillment which will be sent in the ILP Fulfill (response) packet.             |
| destination        | ILP Address | Address of the node that the packet must be delivered to in order to get a valid response (ILP Fulfill).      |

### ILP Fulfill
| Header      | Type    | Description                                                                       |
|-------------|---------|-----------------------------------------------------------------------------------|
| fulfillment | UInt256 | The pre-image of the condition in the corresponding ILP Prepare (request) packet. |

### ILP Reject
| Header      | Type             | Description                                    |
|-------------|------------------|------------------------------------------------|
| code        | 3-char IA5String | An ILP Error code.                             |
| triggeredBy | ILP Address      | The node that triggered the error.             |
| message     | UTF-8 String     | Human-readable message for debugging purposes. |

All packets have a `data` payload which is a variable length octet string up to 32767 bytes.

Like IP packets, the most important header is the **destination.** This is the ILP Address of the node that should receive the packet. However, unlike IP packets, the address of the sender is NOT recorded in the headers. This is because a response packet (ILP Fulfill or ILP Reject) MUST be routed back along exactly the same route as the original request (ILP Prepare) so a receiver has no need for the sender's address as they can simply provide responses in the payload of the response packet.

To correctly route responses, an ILP node must ensure it persists the state of an ILP Prepare packet, at least as long as specified in the **expiresAt** header. When a response to the ILP Prepare is received (either an ILP Fulfill or ILP Reject) from the outgoing link it MUST be routed down the same link on which the ILP Prepare was received. 

If the packet expires before a response is received from the outgoing link then the connecter MUST send an ILP Reject packet as the response on the incoming link. Response packets that are received after the request has expired can be discarded.

The link protocol used to communicate with peers MUST allow the node to match requests and responses such that when a response (ILP Fulfill or ILP Reject) is received from an outgoing link it can be matched to the original.

## ILP Addresses

An ILP packet is addressed using an ILP Address. The ILP Addressing scheme is similar to the IP addressing scheme (both IPv4 and IPv6) in that the scheme is a hierarchical address space where routing is done based on (primarily) longest prefix match of a destination address against the address range prefixes in the node's routing table.

Unlike IP addresses, ILP addresses are variable in size and encoded as IA7 (ASCII) strings of dot (`.`) separated segments. The valid characters in an address segment are alphanumeric plus Underscore (`_`), Tilde (`~`) and Hyphen (`-`) and are case sensitive which allows base64 encoded data to be encoded into address segments.

More details on ILP Addresses are in [ILP RFC 15](https://interledger.org/rfcs/0015-ilp-addresses/).

## Amounts

Amounts in ILP are simple and are represented as 64-bit unsigned integers. As such an amount will have an associated currency and scale which specifies how the integer representation can be converted to a more user friendly decimal form when required.

For example a link between two peers on the network may be settled in US dollars and the peers may decide they wish to allow precision up to 100ths of a cent. In this case the link will be configured by both peers to use the currency USD and the scale of 4. An ILP packet with an amount of 12345 is $1.23,45 or one dollar and twenty-three point four five cents.

# Requirements

## Links

A node must have one or more links to peer nodes with whom it will exchange ILP packets. These links can use any protocol to exchange the packets as long as both peers are able to **correctly correlate which packets are responses to a specific previous request**.

When two peers establish a link they must **agree on the settlement currency and scale for packets exchanged over that link**. The amount in an ILP packet is an unsigned 64-bit number, therefor when a node receives a packet it must infer the currency and scale of the amount from the link on which it was received.

An example of a protocol that can be used between nodes is the [Bilateral Transfer Protocol (BTP)](https://interledger.org/rfcs/0023-bilateral-transfer-protocol/).

## Link Relations

Each link will have one of three relation types which reflect how the node is related to the peer on the other side of the link, these are **peer**, **parent** or **child**. The network graph is organized in a tiered hierarchy, similar to the Internet, reflecting these relationships. Large, high volume nodes are peered with one another to form the backbone of the network. Smaller nodes will have links to these "tier 1" nodes and the link will be of type child from the perspective of the tier 1 node and of type parent from the perspective of the smaller node.

A node MUST only have one link of type parent or, if it has multiple, only one configured to use the IL-DCP protocol upon establishing the link, to request an address from the parent.

A node that has links of type child must host an IL-DCP service to allow the nodes on those links to request addresses. Generally these will be sub-addresses of the node's own address however this is not a requirement.

## Routing

A node must maintain routing information that allows it to determine where to forward incoming packets. Packets arrive on one link and the node must forward the packet out on another link. The logic required to make this determination is not specified but the node SHOULD attempt to forward a packet such that it has the highest probability of being delivered to the node identified by the destination address packet header.

Generally a node will prefer to route packets to a child, over a peer, over a parent as this will likely be the most lucrative for the node. (See [Gao-Rexford](https://people.eecs.berkeley.edu/~sylvia/cs268-2016/papers/gao-rexford.pdf))

Most nodes will maintain a routing table that tracks its **links**, the **address-spaces** that can be delivered to over those links (identified by an address prefix) and the **link relation** of the link. They will attempt to match the destination address of incoming packets with an address prefix in the table to determine the link to forward the packet over. The data in the table is maintained through exchange of routing data by the node with all of it's peers.

When a node's routing data changes in such a way that it is necessary to notify its peers the node will broadcast the changes to all peers. Likewise, the node will continuously be processing incoming updates from its peers.

## Special Addresses

**`peer.*`**

Routing data updates, IL-DCP and other peer-to-peer protocols use ILP packets where the destination address is in the `peer.*` address-space. Nodes that receive packets in the peer.* address-space MUST NOT forward these packets to another node.

**`test.*`, `test1.*`, `test2.*`, and `test3.*`**

A node MUST run either in a test network or on the live network but never on both. If a node is running on the test network it MUST reject all packets in the global address-space, `g.*`. Likewise, if node is running on the live netw    ork it MUST reject any packets with addresses in the `test.*`, `test1.*`, `test2.*`, or `test3.*` address-spaces.
