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

* **[22: Hashed-Timelock Agreements (HTLAs)](0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md)**

  How conditional transfers can be implemented over any type of ledger, including those that do not natively support Hashed-Timelock Contracts.

## Core Interledger Protocol Specs


* **[3: Interledger Protocol (ILP)](0003-interledger-protocol/0003-interledger-protocol.md)**

  Specifies the Interledger Protocol and Interledger Packet, which are used for sending payment instructions across different ledgers and connectors. This is the core protocol in the Interledger stack.

* **[8: Interledger Quoting Protocol (ILQP)](0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md)**

  The protocol for requesting a quote from a connector for an Interledger payment.

* **[15: ILP Addresses](0015-ilp-addresses/0015-ilp-addresses.md)**

  Specifies the Interledger Address format for ledgers and accounts.

## Protocols Built Upon ILP

* **[9: Simple Payment Setup Protocol (SPSP)](0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)**

  A basic Application Layer protocol that uses HTTPS to exchange details needed to set up an Interledger payment.

* **[11: Interledger Payment Request (IPR)](0011-interledger-payment-request/0011-interledger-payment-request.md)**

  A Transport Layer protocol in which the receiver generates the ILP Packet and condition.

* **[16: Pre-Shared Key (PSK)](0016-pre-shared-key/0016-pre-shared-key.md)**

  The recommended Transport Layer protocol for most use cases, which uses a secret shared between the sender and receiver to generate the condition, authenticate the packet, and encrypt application data.

## Ledger Layer

* **[4: Ledger Plugin Interface](0004-ledger-plugin-interface/0004-ledger-plugin-interface.md)**

  Ledger abstraction used in the JavaScript implementation. This can be used as a model for defining such plugins in other languages.

* **[17: Ledger Requirements](0017-ledger-requirements/0017-ledger-requirements.md)**

  Outlines the degrees of Interledger support that different ledgers may provide.

* **[23: Bilateral Transfer Protocol (BTP)](0023-bilateral-transfer-protocol/0023-bilateral-transfer-protocol.md)**

  Recommended API for trustlines and payment channels.

## Routing

* **[10: Connector-To-Connector Protocol (CCP)](0010-connector-to-connector-protocol/0010-connector-to-connector-protocol.md)**

  A protocol used by connectors to communicate routing information.

