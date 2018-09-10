---
title: ILP Addresses
draft: 6
---
# ILP Addresses - v2.0.0

_ILP addresses_ provide a way to [route](#routing) ILP packets to their intended destination through a series of hops, including any number of ILP Connectors. (This happens after address lookup using a higher-level protocol such as [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).) Addresses are not meant to be user-facing, but allow several ASCII characters for easy debugging.

## Routing

Connectors maintain a _routing table_, mapping all of their peer connectors to one or more ILP addresses and address prefixes. 

When a connector receives a prepare packet that is not addressed to itself, it finds the [longest prefix match](https://en.wikipedia.org/wiki/Longest_prefix_match) in its routing table for the destination address. 

The connector determines the appropriate information to put in the _prepare_ packet it forwards to the peer that it matched from the routing table. Later on, the connector expects to get a _fulfill_ or _reject_ packet from its peer. The connector MUST be able to match the prepare packet with this response.

This process continues at the next peer until either some peer accepts the packet and returns a _fulfill_ packet, or a peer rejects the packet by sending a _reject_ packet. If a connector cannot find a more specific match in its routing table, it replies with a _reject_ packet. (There are also other reasons to reject a payment.)

For more detail on the lifecycle and contents of the packets, see the [Interledger Protocol v4 spec](../0027-interledger-protocol-4/0027-interledger-protocol-4.md).

## Address Requirements

ILP Addresses must meet the following requirements:

1. ILP Addresses are made up of one or more segments.
2. Each segment MUST be separated from other segments by a period character (`.`).
3. The first segment MUST indicate the allocation scheme. See [Allocation Schemes](#allocation-schemes) for more information.
4. Each segment MUST contain one or more of the following characters:
    - Alphanumeric characters, upper or lower case. (Addresses are **case-sensitive** so that they can contain data encoded in formats such as base64url.)
    - Underscore (`_`)
    - Tilde (`~`)
    - Hyphen (`-`)
5. Addresses MUST NOT end in a period (`.`) character, and MUST contain at least one segment after the allocation scheme.
6. The total length of an ILP Address must be no more than **1023 characters** including the allocation scheme, separators, and all segments.

The following ABNF specification defines the format for the contents of all ILP addresses and address prefixes. (You must also enforce the overal length requirement of 1023 characters or less.)

```abnf
address     = scheme 1*( separator segment )

scheme      = "g" / "private" / "example" / "peer" / "self" /
              "test" / "test1" / "test2" / "test3" / "local"

separator   = "."

segment     = 1*( ALPHA / DIGIT / "_" / "~" / "-" )
```

You can also use the following regular expressions to verify the same requirements:

    (?=^.{1,1023}$)^(g|private|example|peer|self|test[1-3]?|local)([.][a-zA-Z0-9_~-]+)+$

(If your regular expression engine does not support lookahead, you must drop the first parenthesis and separately enforce the overall length requirement of 1023 characters or less.)

## Allocation Schemes

The allocation scheme is the first part of an address, which indicates how the address is assigned. Here is a summary of the prefixes that are currently defined:

| Prefix                                 | Allocation Scheme               | Definition and Use Case |
|:---------------------------------------|:--------------------------------|:--------------|
| `g.`                                   | [Global Allocation Scheme][]    | ILP addresses that are intended to send and receive money from any other address in the global scheme. |
| `private.`                             | Private allocation              | For ILP addresses that only have meaning in a private subnet or intranet. Analogous to the [192.168.0.0/16 range in IPv4](https://en.wikipedia.org/wiki/Private_network). |
| `example.`                             | Examples                        | For "non-real" addresses that are used as examples or in documentation. Analogous to ["555 phone numbers"](https://en.wikipedia.org/wiki/555_%28telephone_number%29) in the USA. |
|  `test.`, `test1.`, `test2.`, `test3.` | Interledger testnet and testing | For addresses used on the public Interledger testnet and in local tests, such as unit or integration tests of compatible software. |
| `local.`                               | Connector-local                    | For addresses that are only valid in the context of a local connector. Analogous to [link-local addresses](https://en.wikipedia.org/wiki/Link-local_address) in IP. Connectors can use addresses with the `local.` prefix to exchange packets within their own administrative domain, e.g. among a cluster of connectors operated by the same entity. |
| `peer.`                                | Peering                         | Addresses for exchange of packets only with a direct peer. Connectors MUST NOT forward packets with `peer.` addresses. Packets exchanged between peers to pass routing and config information will use `peer.` addresses. |
| `self.`                                | Local loopback                  | For addresses that are only valid on the local machine. |

## Global Allocation Scheme
[Global Allocation Scheme]: #global-allocation-scheme

The global allocation scheme for ILP Addresses is the scheme that most addresses are expected to use. It uses the prefix `g.`. Addresses under this scheme are expected to be connected to all other such addresses, to the extent that the current trust and liquidity permit.

This scheme has no central issuing authority or mechanism, so more than one entity can use the same address. In this case, some connectors may prepare a route to a different account than intended. In this failure case, no money moves because the receiver does not send the fulfillment. Participants in the interledger can reduce the chances of encountering this failure case by choosing addresses carefully and by properly managing connectors' routing tables.

The global allocation scheme does not allow you to make any assumptions about the meaning of the segments. Segments in the same place could have different meanings to different connectors. However, to make routing work well, we recommend placing segments in the following order:

- [Neighborhoods](#neighborhoods)
- [Account identifiers](#account-identifiers)
- [Interactions](#interactions)

Not all addresses contain all this information, and some addresses may use multiple segments to represent some of this information. 

### Neighborhoods

_Neighborhoods_ are leading segments with no specific meaning, whose purpose is to help route to the right area. At this time, there is no official list of neighborhoods, but the following list of examples should illustrate what might constitute a neighborhood:

- `crypto.` for ledgers related to decentralized crypto-currencies such as Bitcoin, Ethereum, or XRP.
- `sepa.` for ledgers in the [Single Euro Payments Area](https://en.wikipedia.org/wiki/Single_Euro_Payments_Area).
- `dev.` for Interledger Protocol development and early adopters

The goal of neighborhoods is to group connectors and ledgers that know about each other, so that routing is more efficient. If a neighborhood is too large or not well-connected, it can be further subdivided into nested sub-neighborhoods. For example, if the `dev.` neighborhood contains too many routes to store efficiently, or if the ledgers in that neighborhood tend only to be connected to other ledgers from the same country, development ledgers hosted in Luxembourg might choose `dev.luxembourg.` as a more closely-knit neighborhood.

### Node Address

The primary function of the ILP address is to facilitate routing of packets to a node on the network. At least one segment must address the node itself. The node address can be multiple segments, which can be useful if the node is a [child](#child-nodes) of a parent connector whose own node address will often prefix the child address.

### Account Identifiers

The _account identifiers_ are one or more segments that serve as a unique identifier of an account held by a connector. The connector maps these to accounts it holds with peers.

### Interactions

_Interactions_ are additional segments after the account identifier portion of an address. Senders and receivers may use a segment (or segments) of an address to indentify contextual properties of the packet exchange.

As an example, the sender may encode the identifier of a shared key in the address allowing the receiver to select the correct key to use for decrypting and/or fulfilling the packet.

### Child Nodes

A node can be addressed relative to another _"parent"_ connector. Smaller and lesser-known connectors may find it easier to advertise routes to themselves in this manner. That way, rather than needing to have their address known to every connector in the same large neighborhood, only the parent connector needs to know how to route to the smaller node.

In most cases a child node will use [ILDCP](#) to get its address from its parent immediately after it has established a connection.

### Example Global Allocation Scheme Addresses

`g.acme.bob` - a destination address to the account "bob" held with the connector "acme".

`g.us-fed.ach.0.acmebank.swx0a0.acmecorp.sales.199.~ipr.cdfa5e16-e759-4ba3-88f6-8b9dc83c1868.2` - destination address for a particular invoice, which can break down as follows:

- Neighborhoods: `us-fed.`, `ach.`, `0.`
- Account identifiers: `acmebank.`, `swx0a0.`, `acmecorp.`, `sales`, `199` (An ACME Corp sales account at ACME Bank)
- Interactions: `~ipr`, `cdfa5e16-e759-4ba3-88f6-8b9dc83c1868`, `2`
