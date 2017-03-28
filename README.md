# Interledger RFCs [![gitter][gitter-img]][gitter-url]

[gitter-img]: https://badges.gitter.im/Join%20Chat.svg
[gitter-url]: https://gitter.im/interledger/Lobby

This repository contains a collection of various specifications and documentation related to the Interledger Protocol (ILP). These documents or requests-for-comment (RFCs) are published by various authors and publication here does not imply official status unless otherwise specified in the document.

## Index

Here is a list of the main Interledger RFCs:

* **[1: Interledger Architecture](0001-interledger-architecture/0001-interledger-architecture.md)**

  Overview of the Interledger architecture.

* **[3: Interledger Protocol (ILP)](0003-interledger-protocol/0003-interledger-protocol.md)**

  Specifies the Interledger Protocol and Interledger Packet, which are used for sending payment instructions across different ledgers and connectors. This is the core protocol in the Interledger stack.

* **[4: Ledger Plugin Interface](0004-ledger-plugin-interface/0004-ledger-plugin-interface.md)**

  JavaScript interface for ledger plugins, which implement all functionality necessary to make Interledger payments through a ledger. This can be used as a model for defining such plugins in other languages.

* **[8: Interledger Quoting Protocol (ILQP)](0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md)**

  Specifies the protocol used for requesting a quote for an Interledger payment from a connector.

* **[9: Simple Payment Setup Protocol (SPSP)](0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md)**

  A basic Application Layer protocol that uses HTTPS to exchange details needed to set up an Interledger payment.

* **[10: Connector-To-Connector Protocol (CCP)](0010-connector-to-connector-protocol/0010-connector-to-connector-protocol.md)**

  The protocol used by connectors to communicate routing information.

* **[11: Interledger Payment Request (IPR)](0011-interledger-payment-request/0011-interledger-payment-request.md)**

  A Transport Layer protocol in which the receiver generates the ILP Packet and condition.

* **[15: ILP Addresses](0015-ilp-addresses/0015-ilp-addresses.md)**

  Specifies the Interledger Address format for ledgers and accounts.

* **[16: Pre-Shared Key (PSK)](0016-pre-shared-key/0016-pre-shared-key.md)**

  The recommended Transport Layer protocol for most use cases, which uses a secret shared between the sender and receiver to generate the condition, authenticate the packet, and encrypt application data.

