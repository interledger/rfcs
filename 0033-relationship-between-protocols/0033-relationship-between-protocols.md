---
title: Relationship between Protocols
draft: 2
---

# Relationship between Protocols

## Prerequisites
This document assumes the reader is familiar with the following document:

- [Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md)

## Terminology
- A **node** is a participant in an Interledger network. It may be a [connector](../0001-interledger-architecture/0001-interledger-architecture.md#connectors), a sender or a receiver.
- A **payment** is sending value from one to another but it doesn't necessarily mean settled, as is explained below. In the Interledger network, a payment could mean a **node-to-node** payment or an **end-to-end** payment.
  - A **node-to-node** payment means the intention of transferring value of a node (a connector, an endpoint sender, or an endpoint receiver) to another node which is directly connected to the sender node.
  - An **end-to-end** payment means the intention of transferring value of an endpoint sender to an endpoint receiver.
- A **settlement** is ensuring that one has the paid value. For instance, executing a transaction on a certain ledger that the payee has an account on.
  - A **node-to-node** payment is settled by means that the two nodes agreed upon. It is usually a ledger that tracks the amount that both nodes have.
  - An **end-to-end** payment is settled through a chain of settlements of intermediaries above, because the end-to-end payment is a chain of node-to-node payments.
  - Payments on the Interledger network could be bidirectional, thus settlements could be as well.
  - Refer to [Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md) and [Perspective](#perspective).

## Motivation
Because the Interledger Protocol suite consists of several protocols and some related specifications, it can be difficult to understand the relationship between each of the protocols. This document attempts to provide an overview and mental model of how the components fit together. It is primarily intended for implementers of parts of the Interledger stack but may also be useful for others who wish to understand how Interledger works as a whole. A mental model is what a reader assumes something to be, reading some explanation. The mental model helps the reader predicting the behavior of what is explained even if the details are not given at that time.

## Scope
The scope of this document is the explication of the relationship between the Interledger protocols, and the details for it are out of scope. Some references are given for it though. i.e. This document draws a whole, big picture of ILP.

## Perspective
There are two diagrams, one is for the macro view that shows the main elements and its IP layer connections, another is for the micro view that shows protocols, the interaction between programs, and the other details.

The alphabets (A-C) and numbers (1-15), that are shown in the diagrams as **red characters**, are explained briefly in the [Elements and Brief Explanations](#elements-and-brief-explanations) section.

### Connections

![Perspective of connections](images/perspective-connections.svg)

### Protocols and Details

This is an enlarged diagram of the above diagram, that shows mainly `Node A`, `Node B`, and `Ledger B`.

![Perspective of connections](images/perspective-protocols.svg)

### Elements and Brief Explanations
#### Connections
- (A) BTP over WebSocket
  - **Node** to **Node** connection
  - In order to exchange payments, configuration and routing information, a node MUST have secure communication channels with its peers. The current implementation uses WebSockets for it.
- (B) Ledger specific connection
  - **Node** to **Ledger** connection
  - A node needs the means to settle its payments. Therefore the node has a connection to a ledger. The type of connection varies depending on the ledger.
  - In the cases where blockchains are used for settlements, nodes MAY utilize payment channels because it is quicker and less expensive than issuing transactions every time the nodes want to settle.
- (C) SPSP over HTTPS
  - **Application** to **SPSP Server** connection
  - To determine end-to-end payment information such as a shared secret, a destination address and so forth, an application connects to SPSP server over HTTPS.

#### Protocols
- Link Layer Protocol
  - (1) BTP
    - [Bilateral Transfer Protocol 2.0 (BTP/2.0)](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md)
    - BTP is used for transferring ILP packets and messages that are used for settlements and so on between two nodes.
- Core ILP Protocols
  - (2) ILP
    - [Interledger Protocol V4 (ILPv4)](../0027-interledger-protocol-4/0027-interledger-protocol-4.md)
    - ILP is used for sending payment packets across multiple hops. Some other protocols, including those for node configuration and routing, are also built on top of ILP and use ILP packets to communicate that information between peers.
  - (3) ILP Address
    - [ILP Addresses](../0015-ilp-addresses/0015-ilp-addresses.md)
    - An ILP address identifies a node.
- Transport Layer Protocol
  - (4) STREAM
    - [STREAM - A Multiplexed Money and Data Transport for ILP](../0029-stream/0029-stream.md)
    - STREAM is a protocol built on top of ILP, and is used for transferring money and data bidirectionally from applications.
- Application Layer Protocols
  - (5) Application
    - Applications MAY build their own protocols on top of STREAM, and put data of the protocols into the extensible data area of STREAM packets.
  - (6) SPSP
    - [The Simple Payment Setup Protocol (SPSP)](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)
    - SPSP is used to determine end-to-end payment information such as a shared secret, a destination address and so forth.
- Connector to Connector Protocol
  - (7) DCP
    - [Interledger Dynamic Configuration Protocol (ILDCP) v1](../0031-dynamic-configuration-protocol/0031-dynamic-configuration-protocol.md)
    - DCP is a protocol built on top of ILP, and is used in order to exchange node information such as an ILP address.
    - DCP data is put into the extensible data area of ILP packets.
  - (8) RBP
    - RBP is a protocol built on top of ILP, and is used for transferring routing information to build routing tables.
    - RBP data is put into the extensible data area of ILP packets.

#### Data Structure and Encoding
- (9) ASN.1
  - [ASN.1 Project](https://www.itu.int/en/ITU-T/asn1/)
  - ASN.1 is used in order to specify data structure (order, type, and length).
  - Concrete packet structure of protocols is defined using ASN.1.
    - [asn1](../asn1/README.md)
- (10) Canonical OER
  - [Notes on OER Encoding](../0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md)
  - ASN.1 doesn't specify its encoding rule. i.e. How packets are encoded in binary is defined separately.
  - Canonical OER is one of the specifications that define the encoding rule.

#### Functions
The functions shown below are just concepts, so their exact form may differ between implementations.

- (11) Account Module
  - An account module manages connections to both a counterpart node and a ledger.
- (12) Bilateral Ledger
  - [Bilateral Transfer Protocol 2.0 (BTP/2.0)](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md#terminology)
  - A bilateral ledger tracks the balance of two nodes connected to each other, including unsettled node-to-node payments.
- (13) Routing Table Module
  - A routing table module aggregates incoming routing information and builds the best routes for prefixes.
- (14) Configuration Module
  - [Interledger Dynamic Configuration Protocol (ILDCP) v1](../0031-dynamic-configuration-protocol/0031-dynamic-configuration-protocol.md)
  - A configuration module retrieves an ILP address that the node should use and the other information from the parent node.
- (15) SPSP Server
  - [The Simple Payment Setup Protocol (SPSP)](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)
  - An SPSP server provides end-to-end payment information such as a shared secret, a destination address and so forth over an HTTPS connection. The SPSP server entity MAY be different from the payee node entity. i.e. The payee node may not serve as an SPSP server.
