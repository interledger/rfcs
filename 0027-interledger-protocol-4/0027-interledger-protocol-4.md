---
title: Interledger Protocol V4 (ILPv4)
draft: 9
---

# Interledger Protocol V4

Interledger is a protocol for sending packets of money across different payment networks or ledgers. ILPv4 is a simplification of previous versions of the protocol that is optimized for routing large volumes of low-value packets, also known as "penny switching". ILPv4 can be integrated with any type of ledger, including those not built for interoperability, and it is designed to be used with a variety of higher-level protocols that implement features ranging from quoting to sending larger amounts of value with chunked payments.

## Overview

### Design Goals

- **Neutrality** - Interledger is not tied to any company, currency, or network.
- **Interoperability** - ILP should be usable across any type of ledger, even those that were not built for interoperability.
- **Security** - Senders, connectors, and receivers should be protected from one another and especially isolated from risks posed by parties that they are indirectly connected to. Connectors should not be able to steal money from senders, and senders should not be able to tie up too much of connectors' funds or otherwise interfere with their operation.
- **Simplicity** - The core ILP should be as simple as possible. There is room for significant variability at lower and higher layers of the [Interledger stack](../0001-interledger-architecture/0001-interledger-architecture.md#interledger-protocol-suite), but the Interledger layer is the one part where widespread agreement is needed for interoperability. Simplifying the core minimizes what people need to agree upon and enables broader adoption.
- **End-to-End Principle** - Inspired by the Internet, any features that do not need to be implemented by the core Interledger Protocol and network of connectors should be built into the edges of the network (the sender and receiver).

### Terminology

- **Account** - Two peers establish an account with one another to track the current obligations they hold with one another.
  * **Balance** - The account balance represents the difference between the value of ILP packets sent and received and the amount of value that has been transferred through an underlying ledger or payment channel (for example, if peer A has signed payment channel updates for 100 units to peer B, peer A sent ILP packets worth 150 units through B, A received ILP packets worth 30 units from B, then peer A owes 20 units to peer B). Each peer maintains their record of the account balance on their own system, or in some cases one peer may trust the other to maintain the account. Connectors may refuse to process further ILP packets if an account balance goes too low.
  * **Asset, Scale, and Precision** - Each account is denominated in a single asset and peers agree on the precision and scale they will use for the amounts of that asset when they express amounts in messages between one another (for example, a scale of 9 means that an amount of 1000000000 in an ILP packet sent between those peers represents 1 unit of that asset). When a connector receives an ILP Prepare packet, they use the asset type and scale of the connection through which the packet was received to determine the meaning of the amount in the packet.
  * **Funding and Rebalancing** - Accounts may be pre-funded (in which case the customer or peer trusts the connector for the value of the account balance) or post-funded (in which case the connector trusts the customer or peer for the amount the account is allowed to go negative).
  * **Difference from "Ledger Accounts"** - Note that the mentions of "accounts" in this document refer to those that Interledger participants _hold with one another_, rather than the "accounts" they may hold on underlying ledgers. Ledger accounts or payment channels are only used for funding and rebalancing Interledger accounts and ledgers are not directly part of the ILPv4 packet flow.
- **Bandwidth** - Connectors may limit the total value of ILP packets an account can send during a given period. The limit may either be based on how much the connector trusts the account-holder, represented by the minimum balance limit on the account, or it may be used to prevent one account from tying up all of the connector's bandwidth with its peers.
- **Condition and Fulfillment** - ILP packets are secured with conditions so that they cannot be lost or stolen by intermediary connectors. ILP Prepare packets contain a condition in the form of a SHA-256 hash. When the receiver receives the packet, they present the fulfillment, in the form of a valid preimage of the condition hash, to execute the transfer. Unlike in earlier versions of ILP, the conditions and fulfillments are NOT assumed to be enforced by the underlying ledger but they help peers reconcile their account balances. Two peers should only consider an ILP packet executed (and therefore affect their account balances) if the fulfillment is a valid preimage of the condition and the fulfillment is received before the Prepare's expiry. See the [Pre-Shared Key V2 (PSKv2)](../0025-pre-shared-key-2/0025-pre-shared-key-2.md) protocol for an example of how a higher-level protocol may generate conditions and fulfillments.
- **ILP Packets** - ILPv4 has three packet types: Prepare, Fulfill, and Reject, which roughly correspond to request, response, and error messages. Connectors forward Prepare packets from senders to receivers and the connectors relay the Fulfill or Reject packets back from the receivers to the senders.
- **Ledger** - A generic term for any system that tracks transfer of value between, and balances on, accounts. In earlier versions of Interledger, ILP packets were transmitted through transfers on ledgers. In ILPv4, ledgers are used primarily to adjust balances between participants, to rebalance their accounts, following the exchange of one or more ILP Packets between the participants.
- **Participant** - A participant in an Interledger payment has accounts with one or more other participants and takes one or more of the following roles:
  * **Sender** - The party that originates payment
  * **Receiver** - The final recipient of a payment
  * **Connector** - The intermediaries between a sender and a receiver that forward ILP Packets. They may generate revenue from spreads on currency conversion, through subscription fees, or other means.
- **Payment** - In the context of this specification, a payment is understood to mean the transfer of value from the sender (payer) to the receiver (payee). Higher-level protocols may execute a "payment" by sending a series of ILP Packets whose sum is equal to the desired payment value.
- **Payment Channel** - A method of using signed claims against funds held on a ledger, rather than on-ledger transfers that may be too slow or expensive, to rebalance accounts. See [Payment Channels in ILPv4](#payment-channels-in-ilpv4) for more details.
- **Peer** - A participant with which another participant holds an account.
- **Transport and Application Layer Protocols** - Senders and receivers generally use higher-level protocols to agree on the condition and other details for each ILP packet. These protocols may also handle encryption and authentication of the data sent with ILP packets. For more details see the [Interledger Architecture overview](../0001-interledger-architecture/0001-interledger-architecture.md#interledger-protocol-suite) or the [Pre-Shared Key V2 (PSKv2)](../0025-pre-shared-key-2/0025-pre-shared-key-2.md) protocol.

### Relation to Other Protocols

ILPv4 packets may be sent over any communication channel between peers. Account balances are adjusted when accepting and forwarding ILP packets and may be rebalanced using any available means, ranging from ledger transfers triggered by an API, to signed updates to payment channels, or the physical delivery of cash or other goods.

ILPv4 will often be used with a Transport Layer protocol, such as the [STREAM](../0029-stream/0029-stream.md) protocol, which handles the generation of ILP conditions and fulfillments. ILPv4 may also be used with higher-level protocols that implement chunking and reassembly of higher-value payments.

### Differences from Previous Versions of ILP

- **Designed for Smaller, More Homogenous Packet Amounts** - ILPv4 applies a number of simplifications by only supporting low-value packets. Larger amounts can be sent through higher-level protocols that implement chunked payments, but the core network is optimized for sending large volumes of small packets. This renders unnecessary some of the more complex features of previous versions like Liquidity Curves for expressing how exchange rates may vary depending on the packet amount. Lower-value packets also help to minimize [connector risks](../0018-connector-risk-mitigations/0018-connector-risk-mitigations.md).
- **Payment Channels, Not On-Ledger Escrow** - Since ILPv4 is optimized for smaller packets, speed and cost are of greater importance than in previous versions. ILPv4 uses ledgers or payment channels for settling bilateral payment obligations but ILPv4 packets are sent just between connectors, rather than through the underlying ledgers themselves. This enables packet timeouts to be short, because they do not need to include the processing time of slower ledgers, which further reduces [connector risks](../0018-connector-risk-mitigations/0018-connector-risk-mitigations.md). See [Why Unconditional Payment Channels](#why-unconditional-payment-channels) for more details.
- **Forwarding, Not Delivery** - ILPv4 connectors forward packets based on their local exchange rates, in contrast with the first version of ILP in which connectors would attempt to deliver a fixed destination amount. Now, instead of fixed destination amount delivery being built into the core protocol, senders may use higher-level protocols to indicate the minimum amount the receiver should accept for a given packet and receivers can reject packets with less than that. This significantly simplifies the connector behavior, because they do not need to maintain up-to-date price information on the entire rest of the network and can simply apply their local rate instead. If receivers want to receive no more than a certain amount, they can reject packets that go too far over the amount and senders can retry the packet with lower amounts.
- **Quoting is an Application Concern** - Connectors are only responsible for forwarding ILP packets and do not need to implement a [separate protocol for quoting](../0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md). Applications can use test packets to determine the exchange rate of a particular path.

### Why Unconditional Payment Channels

The only requirement for ledgers to be integrated with ILPv4 is that they must be able to make simple transfers so that Interledger participants can rebalance their accounts. If ledger transfers are fast and inexpensive, participants can settle their account balances more frequently and set lower trust limits (minimum or maximum account balances) with one another.

Payment channels are a way to use signed claims against funds held on a ledger instead of on-ledger transfers to rebalance accounts. Two peers can sign an unlimited number of updates to their shared payment channel without needing to pay or wait for a potentially expensive or slow on-ledger transfer. For example, they may exchange a signed claim after every ILP packet is fulfilled to keep the trust limit as low as a single packet's value. When the peers are finished interacting, or at some predetermined time, they submit the latest claim to the ledger to split the held funds appropriately between the two participants.

ILPv4 can use [unidirectional](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md#simple-payment-channels) or bidirectional payment channels, but it will most likely NOT use [conditional channels](../0022-hashed-timelock-agreements/0022-hashed-timelock-agreements.md#conditional-payment-channels-with-htlcs) that enforce Hashed Timelock Contracts (HTLCs). Conditional payment channels require participants to account for the ledger's longer processing time in the timeouts for ILP packets. Short timeouts are important for senders to be guaranteed a quick and definitive resolution of their packets. Short timeouts also help connectors limit the risk that malicious senders could tie up their bandwidth or take advantage of the "free option problem" (ensure that packets are held until just before their expiry and then fulfilled only if the exchange rate moved in the sender's favor). In contrast, unconditional payment channels do not require longer timeouts while enabling peers to rebalance frequently and minimize their bilateral trust.

## Flow

### Prerequisites

1. Sender has an account with at least one connector
2. Sender and connector have funds on some shared ledger or settlement system to rebalance their accounts with one another. If the ledger supports payment channels, participants may have unidirectional or bidirectional payment channels open with one another to rebalance their accounts.
3. Sender and connector have an authenticated communication channel through which they will send ILP packets, such as a Secure WebSocket (WSS). Note that connectors use their authenticated communication channels with their peers and customers to determine the source of each packet (packets do not contain the source address).
4. Sender and receiver use a higher-level protocol and/or out-of-band authenticated communication channel to agree on the destination account and packet condition. They may use a protocol like the [Pre-Shared Key V2](../0025-pre-shared-key-2/0025-pre-shared-key-2.md) protocol, which establishes a shared secret and can be used to generate conditions for many packets.

### ILP Packet Lifecycle

1. Sender constructs an ILP Prepare packet with the receiver's destination account, the agreed-upon condition, and an amount and expiry of their choice. The sender may include additional data, the formatting of which is determined by the higher-level protocol.
2. Sender sends the ILP Prepare packet to a connector over their authenticated communication channel.
3. Connector gets the packet and determines which account to debit based on which communication channel it was received through (each account holder will either have an open connection, such as a WebSocket, or each message will be sent with authentication information, such as in an HTTPS request).
4. Connector checks whether the sender has sufficient balance or credit to send the amount specified in the packet. If so, the connector reduces the sender's available balance by the value of the packet. If not, the connector returns an ILP Reject packet.
5. Connector uses its local routing tables and the destination ILP address from the packet to determine which next hop to forward the packet to. The connector may use an exchange orderbook or any other method it chooses to set its exchange rate between the incoming and outgoing assets.
6. Connector modifies the packet amount and expiry to apply their exchange rate and move the expiry timestamp earlier (for example, each connector may subtract one second from the expiry to give themselves a minimum of one second to pass the Fulfill on in step 10).
7. Connector forwards the packet to the next hop, which may be another connector. All subsequent connectors go through steps 3-7 (treating the previous connector as the sender) until the packet reaches the receiver.
8. Receiver checks the ILP Prepare packet, according to whatever is stipulated by the higher-level protocol (such as checking whether the amount received is above some minimum specified by the sender). Receiver also checks that the Prepare would not put the connector's unsettled balance above the maximum the receiver tolerates (this is the same as the minimum balance limit of the connector _with the receiver_).
9. To accept the packet, the receiver returns an ILP Fulfill packet, containing the preimage of the condition in the ILP Prepare packet. The receiver sends the Fulfill back through the same communication channel the Prepare packet was received from. The receiver may include additional data in the Fulfill packet, the formatting of which is determined by the higher-level protocol. If the receiver does not want the ILP Prepare packet or it does not pass one of the checks, the receiver returns an ILP Reject packet instead.
10. If the receiver returned an ILP Fulfill, the connector checks that the fulfillment hashes to the original condition and that the receiver returned it before the expiry in the ILP Prepare packet. If the fulfillment is valid, the connector returns the same ILP Fulfill packet to the previous connector (using the same communication channel they originally received the ILP Prepare from) and the connector credits the receiver's account with the amount in the original ILP Prepare packet. If the receiver returned an ILP Reject packet or the Prepare expired before the Fulfill was returned, the connector returns an ILP Reject packet to the previous connector (note that connectors SHOULD return ILP Reject packets when the Prepare expires, even if they have not yet received a response from the next participant). Each connector repeats this step (crediting the account of the participant that returned the Fulfill) until the Fulfill (or Reject) packet reaches the sender.
11. Sender checks that the preimage in the ILP Fulfill packet matches the condition in their Prepare packet and may read any data returned by the receiver. The sender may keep a local record of the total value of packets fulfilled to determine how much they owe their connector.
12. Sender repeats the process, starting from step 1, as many times as is necessary to transfer the desired total amount of value.

### Rebalancing Accounts

Participants may have pre-funded or post-funded accounts with one another.

In the case of pre-funded accounts, senders send some amount to their connector to cover packets they will send. Senders can use transfers on an underlying ledger, payment channel updates, or any other means to send value to the connector. Senders can pre-fund their accounts as much or as little as they choose based on how much they trust the connector to forward ILP packets for them and the volume of packets the sender expects to send.

In the case of post-funded accounts, senders transfer value to their connector after they have received the fulfillments for one or more outgoing ILP packets. If participants use payment channels, they may choose to sign an update to the payment channel to cover the value of each packet sent and thus minimize the amount the connector must trust the sender for. If participants use some other means of rebalancing, such as transfers on a slower ledger or delivery of physical assets, they may wish to rebalance their accounts less frequently and settle for larger amounts.

## Specification

### Packet Format

ILPv4 packets MUST be encoded using the ASN.1 Canonical Octet Encoding Rules. Implementations MAY accept packets encoded in a non-canonical form.

#### Type-Length Wrapper

All ILP packets are wrapped in the following envelope:

| Field | Type | Description |
|---|---|---|
| `type` | UInt8 | ID of the ILP Packet type |
| `data` | Variable-Length Octet String | Packet contents, prefixed with their length |

See the ASN.1 definition [here](../asn1/InterledgerPacket.asn).

#### ILP Prepare

ILP Prepare packets are `type` 12.

The `amount` and `expiresAt` are fixed-length fields so that they may be modified in-place (without copying the rest of the packet) by each connector. These are the only fields that are modified by connectors as the packet is forwarded.

| Field | Type | Description |
|---|---|---|
| `amount` | UInt64 | Local amount, denominated in the minimum divisible unit of the asset of the bilateral relationship. This field is modified by each connector, who applies their exchange rate and adjusts the amount to the appropriate scale and precision of the outgoing account |
| `expiresAt` | Fixed-Length [Interledger Timestamp](../asn1/InterledgerTypes.asn) | Date and time when the packet expires. Each connector changes the value of this field to set the expiry to an earlier time, before forwarding the packet. |
| `executionCondition` | UInt256 | SHA-256 hash digest of the `fulfillment` that will execute the transfer of value represented by this packet. Connectors MUST NOT modify this field. The receiver must be able to fulfill this condition to receive the money. |
| `destination` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the receiver |
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data. Most higher-level protocols will encrypt and authenticate this data, so receivers will reject packets in which the data is modified |

**Note:** There is no `from` or `source` address in the ILP Prepare packet. Each hop MUST determine which of their immediate peers or customers the packet came from (to debit the correct account) based on the _authenticated_ communication channel the packet was received through. Also, higher-level protocols MAY communicate the sender's address to the receiver if the use case calls for receivers to send ILP Prepare packets to the sender (they can communicate responses to the sender using the `data` field in ILP Fulfill and Reject packets).

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

#### ILP Fulfill

ILP Fulfill packets are `type` 13.

| Field | Type | Description |
|---|---|---|
| `fulfillment` | UInt256 | 32-byte preimage of the `executionCondition` from the corresponding ILP Prepare packet |
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data |

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

#### ILP Reject

ILP Reject packets are `type` 14.

| Field | Type | Description |
|---|---|---|
| `code` | 3-Character IA5String | [ILP Error Code](#error-codes) |
| `triggeredBy` | [ILP Address](../0015-ilp-addresses/0015-ilp-addresses.md) | ILP Address of the party that created this error |
| `message` | UTF8 String | User-readable error message, primarily intended for debugging purposes |
| `data` | Variable-Length Octet String | End-to-end data. Connectors MUST NOT modify this data |

See the ASN.1 definition [here](../asn1/InterledgerProtocol.asn).

### Error Codes

#### F__ - Final Error

Final errors indicate that the payment is invalid and should not be retried unless the details are changed.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **F00** | **Bad Request** | Generic sender error. | (empty) |
| **F01** | **Invalid Packet** | The ILP packet was syntactically invalid. | (empty) |
| **F02** | **Unreachable** | There was no way to forward the payment, because the destination ILP address was wrong or the connector does not have a route to the destination. | (empty) |
| **F03** | **Invalid Amount** | The amount is invalid, for example it contains more digits of precision than are available on the destination ledger or the amount is greater than the total amount of the given asset in existence. | (empty) |
| **F04** | **Insufficient Destination Amount** | The receiver deemed the amount insufficient, for example, the effective exchange rate was too low. | (empty) |
| **F05** | **Wrong Condition** | The receiver generated a different condition and cannot fulfill the payment. | (empty) |
| **F06** | **Unexpected Payment** | The receiver was not expecting a payment like this (the data and destination address don't make sense in that combination, for example if the receiver does not understand the transport protocol used) | (empty) |
| **F07** | **Cannot Receive** | The receiver (beneficiary) is unable to accept this payment due to a constraint. For example, the payment would put the receiver above its maximum account balance. | (empty) |
| **F08** | **Amount Too Large** | The packet amount is higher than the maximum a connector is willing to forward. Senders MAY send another packet with a lower amount. Connectors that produce this error SHOULD encode the amount they received and their maximum in the `data` to help senders determine how much lower the packet amount should be. | See [ASN.1](../asn1/InterledgerErrorData.asn) |
| **F99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |

#### T__ - Temporary Error

Temporary errors indicate a failure on the part of the receiver or an intermediary system that is unexpected or likely to be resolved soon. Senders SHOULD retry the same payment again, possibly after a short delay.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **T00** | **Internal Error** | A generic unexpected exception. This usually indicates a bug or unhandled error case. | (empty) |
| **T01** | **Peer Unreachable** | The connector has a route or partial route to the destination but was unable to reach the next connector. Try again later. | (empty) |
| **T02** | **Peer Busy** | The next connector is rejecting requests due to overloading. If a connector gets this error, they SHOULD retry the payment through a different route or respond to the sender with a `T03: Connector Busy` error. | (empty) |
| **T03** | **Connector Busy** | The connector is rejecting requests due to overloading. Try again later. | (empty) |
| **T04** | **Insufficient Liquidity** | The connector would like to fulfill your request, but either the sender or a connector does not currently have sufficient balance or bandwidth. Try again later. | (empty) |
| **T05** | **Rate Limited** | The sender is sending too many payments and is being rate-limited by a ledger or connector. If a connector gets this error because they are being rate-limited, they SHOULD retry the payment through a different route or respond to the sender with a `T03: Connector Busy` error. | (empty) |
| **T99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |

#### R__ - Relative Error

Relative errors indicate that the payment did not have enough of a margin in terms of money or time. However, it is impossible to tell whether the sender did not provide enough error margin or the path suddenly became too slow or illiquid. The sender MAY retry the payment with a larger safety margin.

| Code | Name | Description | Data Fields |
|---|---|---|---|
| **R00** | **Transfer Timed Out** | The transfer timed out, meaning the next party in the chain did not respond. This could be because you set your timeout too low or because something took longer than it should. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. | (empty) |
| **R01** | **Insufficient Source Amount** | The amount received by a connector in the path was too little to forward (zero or less). Either the sender did not send enough money or the exchange rate changed. The sender MAY try again with a higher amount, but they SHOULD NOT do this indefinitely or a malicious connector could steal money from them. | (empty) |
| **R02** | **Insufficient Timeout** | The connector could not forward the payment, because the timeout was too low to subtract its safety margin. The sender MAY try again with a higher expiry, but they SHOULD NOT do this indefinitely or a malicious connector could cause them to tie up their money for an unreasonably long time. | (empty) |
| **R99** | **Application Error** | Reserved for application layer protocols. Applications MAY use names other than `Application Error`. | Determined by Application |
