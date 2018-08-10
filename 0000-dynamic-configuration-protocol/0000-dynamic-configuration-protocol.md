---
title: Interledger Dynamic Configuration Protocol
draft: 1
---

# Interledger Dynamic Configuration Protocol (ILDCP)

## Prerequisite
Before looking into this document, reading the following documents is highly recommended to understand the prerequisite knowledge.

- [Interledger Architecture](../0001-interledger-architecture/0001-interledger-architecture.md)
- [Interledger Protocol V4 (ILPv4)](../0027-interledger-protocol-4/0027-interledger-protocol-4.md)

## Terminology

- A **node** represents a [connector](../0001-interledger-architecture/0001-interledger-architecture.md#connectors) in this document. Nodes are connected each other and the relationship between two nodes is described as the below.
  - `parent` and `child`, one node is the `parent` of another node that is relatively `child`.
  - `peer` and `peer`, two nodes are connected equally.

## Overview
Interledger Protocol is a protocol suite that consists of several protocols including [Bilateral Transfer Protocol](../0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md), Route Broadcasting Protocol and the other protocols. Dynamic Configuration Protocol (ILDCP) is one of them.

A node must have its ILP address to make the other nodes route ILP packet appropriately. Therefore those who run a node have to specify the ILP address of the node when start it up. If the node is a child of a certain node, the ILP address that the child node should use can be automatically given by the parent node using ILDCP so that the child node doesn't need to specify it.

In short, **ILDCP is a protocol used for transferring node and ledger information from a parent node to a child node**. The transferred information is:

- An ILP address that the child should use for its own address
  - e.g. `g.crypto.foo.bar`
- An asset code of the ledger that the two nodes will use
  - e.g. `XRP`
- An asset scale of the ledger that the two nodes will use
  - e.g. `6`

## Protocol Detail

### Procedure
Acquisition is done in the following procedure.

1. A child node requests information to the corresponded parent node
2. The parent node responds information to the child node
3. If the request can not be deserialized and interpreted as appropriate, the parent node should respond error

### Packet
The request and the response above are transferred in [ILP packets](../0027-interledger-protocol-4/0027-interledger-protocol-4.md#specification) in a specific manner. The manner is:

- Request
  - The `type` of the ILP packet is `ILP Prepare` (type id: 12)
  - The `amount` of the ILP packet is `0`
  - The `expiresAt` of the ILP packet is arbitrary
  - The `executionCondition` of the ILP packet is `Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=` in Base64 format
  - The `destination` address of the ILP packet is `peer.config`
  - The `data` of the ILP packet is empty (size: 0)
- Response
  - The `type` of the ILP packet is `ILP Fulfill` (type id: 13)
  - The `fulfillment` of the ILP packet is 32byte octet string all filled with zeros
  - The `data` of the ILP packet is the below in the exact order:
    - `Variable-length octet string`: ILP address that the child should use, that can be decoded in `ASCII` format
    - `Uint8`: asset scale
    - `Variable-length octet string`: asset code, that can be decoded in `UTF-8` format
- Error
  - The `type` of the ILP packet is `ILP Reject` (type id: 14)
  - The `code` of the ILP packet is arbitrary, depending on the situation
  - The `message` of the ILP packet is arbitrary, depending on the situation
  - The `triggeredBy` of the ILP packet is the ILP address of the parent node
  - The `data` of the ILP packet is empty (size: 0)

### Encoding Rule
The ASN.1 definition of ILP packet is described in [InterledgerProtocol.asn](../asn1/InterledgerProtocol.asn). How the variable-length octet string and Uint8 are written into binary is described in [Notes on OER Encoding](../0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md).