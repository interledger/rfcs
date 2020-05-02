---
title: Interledger Dynamic Configuration Protocol
draft: 3
---

# Interledger Dynamic Configuration Protocol (ILDCP) v1

## Prerequisites
This specification assumes the reader is familiar with the following documents:

- [Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md)
- [Interledger Protocol V4 (ILPv4)](../0027-interledger-protocol-4/0027-interledger-protocol-4.md)

## Terminology

- A **node** is a participant in an Interledger network. It may be a [connector](../0001-interledger-architecture/0001-interledger-architecture.md#connectors), a sender or a receiver. 
- Nodes are connected to each other and the relationship between two nodes is either:
  - `parent` and `child` (one node is the `parent` of another node that is relatively its `child`), or,
  - `peer` and `peer` (two nodes are peered with one another).

## Overview
Interledger is a protocol suite that consists of several protocols including the [Bilateral Transfer Protocol](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md), the Route Broadcasting Protocol and others necessary for establishment, operation and maintenance of the network. Interledger Dynamic Configuration Protocol (ILDCP) is one of these protocols.

In order to participate in the network a node must have an [ILP address](../0015-ilp-addresses/0015-ilp-addresses.md). This address is part of a heirarchical address space where child nodes MAY be allocated addresses within the address space of their parent node. This makes routing on the network more efficient than if all nodes had top-level addresses.

A node is therefore either configured with an address which it broadcasts to its peers or, if the node has a parent in the network hierarchy, the ILP address of the child node can be allocated to it by the parent. This is done using ILDCP.

In short, **ILDCP is a protocol used for transferring node and ledger information from a parent node to a child node**. The transferred information is:

- An ILP address that the child should use for its own address
  - e.g. `g.crypto.foo.bar`
- An asset code of the asset that the two nodes will use to settle
  - e.g. `XRP`
- An asset scale for amounts that will be used in ILP packets exchanged between the nodes.
  - e.g. `6`

Future versions of the protocol MAY exchange additional configuration information.

## Protocol Detail

### Procedure
An exchange of configuration information is done using the following procedure.

1. A child node requests configuration information from the parent node
2. The parent node responds with the configuration information to the child node
3. If the request cannot be processed, the parent node responds with an error

### Packet
The request and the response above are transferred in [ILP packets](../0027-interledger-protocol-4/0027-interledger-protocol-4.md#specification). 

The `fulfillment` of the response packet is always a zero-filled 32 byte octet string, therefore the condition is always the SHA-256 hash digest of that, i.e. the Base64 decoded value of `Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=`.

As with other bilateral protocols the packets are addressed directly to the peer using the `peer.` address prefix. ILDCP packets are specifically identified using the address `peer.config`.

All current implementations of ILDCP default to an amount of `0` in the ILP packets used to request configuration. In future, peers may agree to pay a charge for reserving an address, in which case this may become a non-zero amount indicating the amount paid by the child to reserve an address. Future version of the protocol may allow for the child to explicitly request an address which may not be restricted to being in the parent's address-space.

The packet exchange goes as follows:

- Request
  - The `type` of the ILP packet is `ILP Prepare` (type id: 12)
  - The `amount` of the ILP packet defaults to `0`.
  - The `expiresAt` of the ILP packet is arbitrary.
  - The `executionCondition` of the ILP packet is `Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=` in Base64 format
  - The `destination` address of the ILP packet is `peer.config`
  - The `data` of the ILP packet is empty (size: 0)
  
- Response
  - The `type` of the ILP packet is `ILP Fulfill` (type id: 13)
  - The `fulfillment` of the ILP packet is a 32-byte octet string all filled with zeros
  - The `data` of the ILP packet takes a specific format and is described by `DynamicConfigurationResponseData` in the ILDCP [ASN.1 definition](#asn1-definition). It is an OER encoded SEQUENCE of
    - `Variable-length octet string`: An ILP address that the child should use, encoded as an `ASCII` string
    - `Uint8`: An unsigned 8-bit integer indicating the asset scale that should be used for packets exchanged with the parent
    - `Variable-length octet string`: An asset code, encoded as a `UTF-8` string, indicating the settlement asset used between the peers
    
- Error
  - The `type` of the ILP packet is `ILP Reject` (type id: 14)
  - The `code` of the ILP packet is an appropriate error code
  - The `message` of the ILP packet is an appropriate human-readable message for debugging purposes
  - The `triggeredBy` of the ILP packet is the ILP address of the parent node
  - The `data` of the ILP packet is empty (size: 0) or MAY contain further information for debugging the error.

### ASN.1 Definition
The ASN.1 definition of ILP packets is described in [InterledgerProtocol.asn](../asn1/InterledgerProtocol.asn) and Dynamic Configuration Protocol data in [DynamicConfigurationProtocol.asn](../asn1/DynamicConfigurationProtocol.asn).

### Encoding
All ASN.1 types are encoded using [Octet Encoding Rules](../0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md) as is the norm with all Interledger protocols.
