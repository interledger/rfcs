# Interledger RFCs [![gitter][gitter-img]][gitter-url]

[gitter-img]: https://badges.gitter.im/Join%20Chat.svg
[gitter-url]: https://gitter.im/interledger/Lobby

This repository contains a collection of various specifications and documentation related to the Interledger Protocol (ILP). These documents or requests-for-comment (RFCs) are published by various authors and publication here does not imply official status unless otherwise specified in the document.

The process for submitting an RFC is documented in the [RFC Process](CONTRIBUTING.md).

For the main reference implementation of the ILP stack, see [Interledger.js](https://github.com/interledgerjs).

## Interledger Overview and Explanatory Docs

* **[1: Interledger Architecture](0001-interledger-architecture/0001-interledger-architecture.md)**

  Overview of the Interledger architecture.

* **[19: Glossary](./0019-glossary/0019-glossary.md)**

  Definitions of Interledger terminology.

* **[20: Explain Like I'm Five (ELI5)](0020-explain-like-im-five/0020-explain-like-im-five.md)**

  Basic explanation of Interledger.

## Core Interledger Protocol Specs


* **[27: Interledger Protocol V4 (ILPv4)](0027-interledger-protocol-4/0027-interledger-protocol-4.md)**

  Specifies the Interledger Protocol and Interledger Packet, which are used for sending payment instructions across different ledgers and connectors. This is the core protocol in the Interledger stack.

* **[15: ILP Addresses](0015-ilp-addresses/0015-ilp-addresses.md)**

  Specifies the Interledger Address format for ledgers and accounts.

## Protocols Built Upon ILP

* **[29: Loopback Transport (LT) and Loopback Server Discovery (LSD)](0029-loopback-transport/0029-loopback-transport.md)**

  One of the recommended Transport Layer protocols for most use cases, which handles quoting, individual payments, chunked payments, and streaming payments using a loopback link between the sender and receiver.

* **[9: Simple Payment Setup Protocol (SPSP)](0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)**

  A basic Application Layer protocol that uses HTTPS to exchange details needed to set up an Interledger payment.

* **[25: Pre-Shared Key V2 (PSKv2)](0025-pre-shared-key-2/0025-pre-shared-key-2.md)**

  A more advanced Transport Layer protocol which uses a shared secret to establish a virtualized end-to-end link between the sender and receiver.


## Ledger Layer

* **[24: Ledger Plugin Interface V2](0024-ledger-plugin-interface-2/0024-ledger-plugin-interface-2.md)**

  Ledger abstraction used in the JavaScript implementation. This can be used as a model for defining such plugins in other languages.

* **[23: Bilateral Transfer Protocol (BTP)](0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md)**

  Recommended API for trustlines and payment channels.

## Routing

* **[10: Connector-To-Connector Protocol (CCP)](0010-connector-to-connector-protocol/0010-connector-to-connector-protocol.md)**

  A protocol used by connectors to communicate routing information.

