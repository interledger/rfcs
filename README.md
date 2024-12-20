# Interledger RFCs [![gitter][gitter-img]][gitter-url]

[gitter-img]: https://badges.gitter.im/Join%20Chat.svg
[gitter-url]: https://gitter.im/interledger/Lobby

This repository contains a collection of various specifications and documentation related to the Interledger Protocol (ILP). These documents or requests-for-comment (RFCs) are published by various authors and publication here does not imply official status unless otherwise specified in the document.

The process for submitting an RFC is documented in the [RFC Process](CONTRIBUTING.md).

For the main reference implementation of the ILP stack, see [Interledger.js](https://github.com/interledgerjs).

## Deprecation Notice

**Warning: This feature is deprecated and will be removed in future versions.**

Please avoid using this feature in new projects. Instead, consider using the recommended alternative:

- 0002-crypto-conditions
- 0003-interledger-protocol
- 0004-ledger-plugin-interface
- 0005-optimistic-transport-protocol
- 0006-universal-transport-protocol
- 0007-atomic-transport-protocol
- 0008-interledger-quoting-protocol
- 0008-interledger-quoting-protocol
- 0010-connector-to-connector-protocol
- 0011-interledger-payment-request
- 0012-five-bells-ledger-api
- 0014-paid-http-apis
- 0016-pre-shared-key
- 0017-ledger-requirements
- 0020-explain-like-im-five
- 0021-plugin-rpc-api
- 0024-ledger-plugin-interface-2
- 0025-pre-shared-key-2
- 0028-web-monetization
- 0036-spsp-pull-payments
- 0037-spsp-invoices

## ASN.1 and OER

A number of the protocols define data structures in ASN.1 notation. The collection of definitions is in [asn1](./asn1).

Changes to these files are automatically checked and compiled during CI using online ASN.1 tools from OSS Nokalva. If you need ASN.1 tools for any work you're doing on Interledger please contact them for assistance.

[![OSS Nokalva](https://raw.githubusercontent.com/interledger/rfcs/master/assets/osslogo.png)](http://asn1-playground.oss.com/)

You can also check your ASN.1 definitions online using OSS Nokalva's ASN.1 Playground available at http://asn1.io/

The default encoding rules for Interledger protocols are the Canonical Octet Encoding Rules as described in [Notes on OER encoding](./0030-notes-on-oer-encoding/0030-notes-on-oer-encoding.md).

## Interledger Overview and Explanatory Docs

- **[1: Interledger Architecture](0001-interledger-architecture/0001-interledger-architecture.md)**

  Overview of the Interledger architecture.

- **[19: Glossary](./0019-glossary/0019-glossary.md)**

  Definitions of Interledger terminology.

## Core Interledger Protocol Specs

- **[27: Interledger Protocol V4 (ILPv4)](0027-interledger-protocol-4/0027-interledger-protocol-4.md)**

  Specifies the Interledger Protocol and Interledger Packet, which are used for sending payment instructions across different ledgers and connectors. This is the core protocol in the Interledger stack.

- **[15: ILP Addresses](0015-ilp-addresses/0015-ilp-addresses.md)**

  Specifies the Interledger Address format for ledgers and accounts.

## Protocols Built Upon ILP

- **[9: Simple Payment Setup Protocol (SPSP)](0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)**

  A basic Application Layer protocol that uses HTTPS to exchange details needed to set up an Interledger payment.

- **[29: STREAM](0029-stream/0029-stream.md)**

  The recommended Transport Layer protocol for most use cases, which handles quoting, individual payments, chunked payments, and streaming payments using a shared secret between the sender and receiver.

## Ledger Layer

- **[38: Settlement Engines](0038-settlement-engines/0038-settlement-engines.md)**

  Specifies an interface to send and receive payments across different settlement systems and ledgers.
