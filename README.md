# Interledger RFCs [![gitter][gitter-img]][gitter-url]

[gitter-img]: https://badges.gitter.im/Join%20Chat.svg
[gitter-url]: https://gitter.im/interledger/Lobby

This repository contains a collection of various specifications and documentation related to the Interledger Protocol (ILP). These documents or requests-for-comment (RFCs) are published by various authors and publication here does not imply official status unless otherwise specified in the document.

The process for submitting an RFC is documented in the [RFC Process](CONTRIBUTING.md).

For the main reference implementation of the ILP stack, see [Interledger.js](https://github.com/interledgerjs).

## ASN.1 and OER

A number of the protocols define data structures in ASN.1 notation. The collection of definitions is in [asn1](./asn1).

Changes to these files are automatically checked and compiled during CI using online ASN.1 tools from OSS Nokalva. If you need ASN.1 tools for any work you're doing on Interledger please contact them for assistance.

[![OSS Nokalva](./assets/osslogo.png)](http://asn1-playground.oss.com/)

You can also check your ASN.1 definitions online using OSS Nokalva's ASN.1 Playground available at http://asn1.io/

The default encoding rules for Interledger protocols are the Canonical Octet Encoding Rules as described in [Notes on OER encoding](./0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md).

## Interledger Overview and Explanatory Docs

* **[1: Interledger Architecture](0001-interledger-architecture/0001-interledger-architecture.md)**

  Overview of the Interledger architecture.

* **[19: Glossary](./0019-glossary/0019-glossary.md)**

  Definitions of Interledger terminology.

## Core Interledger Protocol Specs


* **[27: Interledger Protocol V4 (ILPv4)](0027-interledger-protocol-4/0027-interledger-protocol-4.md)**

  Specifies the Interledger Protocol and Interledger Packet, which are used for sending payment instructions across different ledgers and connectors. This is the core protocol in the Interledger stack.

* **[15: ILP Addresses](0015-ilp-addresses/0015-ilp-addresses.md)**

  Specifies the Interledger Address format for ledgers and accounts.

## Protocols Built Upon ILP

* **[9: Simple Payment Setup Protocol (SPSP)](0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)**

  A basic Application Layer protocol that uses HTTPS to exchange details needed to set up an Interledger payment.

* **[29: STREAM](0029-stream/0029-stream.md)**

  The recommended Transport Layer protocol for most use cases, which handles quoting, individual payments, chunked payments, and streaming payments using a shared secret between the sender and receiver.

## Ledger Layer

* **[24: Ledger Plugin Interface V2](0024-ledger-plugin-interface-2/0024-ledger-plugin-interface-2.md)**

  Ledger abstraction used in the JavaScript implementation. This can be used as a model for defining such plugins in other languages.

* **[23: Bilateral Transfer Protocol (BTP)](0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md)**

  Recommended API for trustlines and payment channels.

