# ILP Addresses

_ILP addresses_ provide a way to [route](#routing) payments to their intended destination through a recursive series of hops, including any number of ILP Connectors. (This happens after the payment is set up on by a higher-level payment setup protocol such as [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).) Addresses are not meant to be user-facing, but allow several ASCII characters for easy debugging.

Addresses can be subdivided into two categories:

- **Destination Addresses** are complete addresses that can receive payments. A destination address always maps to one account in a ledger. (It can also provide more specific information, such as an invoice ID or a sub-account.) Destination addresses MUST NOT end in a period (`.`) character.
- **Address Prefixes** are incomplete addresses representing a group of destination addresses. Many depths of grouping are possible: groups of accounts or sub-accounts, an individual ledger or subledger, or entire neighborhoods of ledgers. Address prefixes MUST end in a period (`.`) character. Payment setup protocols MUST reject payments to address prefixes.

Both types of address usually contain one or more period characters as separators.

## Routing

Connectors maintain a _routing table_ of ILP addresses. Routing is a recursive lookup through the routing tables of any number of connectors. When a connector receives a query, it finds the [longest prefix match](https://en.wikipedia.org/wiki/Longest_prefix_match) for the queried address. Then, it follows one of the following cases:

- If the matching address is marked for local delivery, the connector prepares a transfer to that address in one of the ledgers connected to it. The connector's ledger plugin maps the ILP address to an account within the ledger. (This is the base case.)
- If the matching address is marked as forwarded delivery, it has the address of another connector associated with it in the routing table. The connector makes a routing lookup on the connector associated with the address. (This is the recursive case.)

## Address Requirements

ILP Addresses must meet the following requirements:

1. The address MUST begin with a prefix indicating the allocation scheme. See [Allocation Schemes](#allocation-schemes) for more information.
2. Each "segment" of the address MUST contain one or more of the following characters:
    - Alphanumeric characters, upper or lower case. (Addresses are **case-sensitive** so that they can contain data encoded in formats such as base64url.)
    - Underscore (`_`)
    - Tilde (`~`)
    - Hyphen (`-`)
3. Each segment MUST be separated from other segments by a period character (`.`).
4. Address prefixes MUST end in a period (`.`) character and MAY contain any number of segments after the allocation scheme prefix.
5. Destination addresses MUST NOT end in a period (`.`) character, and MUST contain at least two segments after the allocation scheme prefix.

The following ABNF specification defines the format for all ILP addresses and address prefixes:

```abnf
address     = scheme separator *prefix [segment]
                    ; the last segment is REQUIRED for destination addresses

scheme      = "g" / "private" / "example" / "peer" / "self" /
              "test1" / "test2" / "test3"

separator   = "."

prefix      = 1*(segment separator)

segment     = 1*( ALPHA / DIGIT / "_" / "~" / "-" )
```

You can also use the following regular expressions to verify the same requirements:

| Address Type        | Regular Expression                                     |
|:--------------------|:-------------------------------------------------------|
| All addresses       | `^(g|private|example|peer|self|test[1-3])\.([a-zA-Z0-9_~-]+\.)*([a-zA-Z0-9_~-]+)?$` |
| Address prefix      | `^(g|private|example|peer|self|test[1-3])\.([a-zA-Z0-9_~-]+\.)*$` |
| Destination address | `^(g|private|example|peer|self|test[1-3])\.([a-zA-Z0-9_~-]+\.)+[a-zA-Z0-9_~-]+$` |


## Allocation Schemes

The allocation scheme is the first part of an address, which indicates how the address is assigned. Here is a summary of the prefixes that are currently defined:

| Prefix                       | Allocation Scheme             | Definition and Use Case |
|:-----------------------------|:------------------------------|:--------------|
| `g.`                         | [Global Allocation Scheme][]  | ILP addresses that are intended to send and receive money from any other address in the global scheme. |
| `private.`                   | Private allocation            | For ILP addresses that only have meaning in a private subnet or intranet. Analogous to the [192.168.0.0/16 range in IPv4](https://en.wikipedia.org/wiki/Private_network). |
| `example.`                   | Examples                      | For "non-real" addresses that are used as examples or in documentation. Analogous to ["555 phone numbers"](https://en.wikipedia.org/wiki/555_%28telephone_number%29) in the USA. |
| `test1.`, `test2.`, `test3.` | Testing                       | For addresses used in tests, such as unit or integration tests of compatible software. |
| `local.`                     | Ledger-local                  | For addresses that are only valid in the context of a local ledger. Analogous to [link-local addresses](https://en.wikipedia.org/wiki/Link-local_address) in IP. |
| `peer.`                      | Peering                       | Similar to ledger-local addresses, but specifically for use in a peering relationship. The [ilp-plugin-virtual](https://github.com/interledgerjs/ilp-plugin-virtual) is an example of an existing implementation that uses this. |
| `self.`                      | Local loopback                | For addresses that are only valid on the local machine. |

## Global Allocation Scheme
[Global Allocation Scheme]: #global-allocation-scheme

The global allocation scheme for ILP Addresses is the scheme that most addresses are expected to use. It uses the prefix `g.`. Addresses under this scheme are expected to be connected to all other such addresses, to the extent that the current trust and liquidity permit.

This scheme has no central issuing authority or mechanism, so more than one entity can use the same address. In this case, some connectors may prepare a route to a different account than intended. In this failure case, no money moves because the receiver does not send the fulfillment. Participants in the interledger can reduce the chances of encountering this failure case by choosing addresses carefully and by properly managing connectors' routing tables.

The global allocation scheme does not allow you to make any assumptions about the meaning of the segments. Segments in the same place could have different meanings to different ledgers or connectors. However, to make routing work well, we recommend placing segments in the following order:

- [Neighborhoods](#neighborhoods)
- [Ledger prefixes](#ledger-prefixes)
- [Account identifiers](#account-identifiers)
- [Interactions](#interactions)

Not all addresses contain all this information, and some addresses may use multiple segments to represent some of this information.

### Neighborhoods

Neighborhoods have no specific meaning, but serve as a quick shortcut for routing to the right area. At this time, there is no official list of neighborhoods, but the following list of examples should illustrate what might constitute a neighborhood:

- `crypto.` for ledgers related to decentralized crypto-currencies such as Bitcoin, Etherium, or XRP.
- `sepa.` for ledgers in the [Single Euro Payments Area](https://en.wikipedia.org/wiki/Single_Euro_Payments_Area).
- `dev.` for Interledger Protocol development and early adopters

Large neighborhoods can be further subdivided into nested sub-neighborhoods; for example, `dev.luxembourg.` for development ledgers hosted in Luxembourg.


### Ledger Prefixes

A ledger prefix is the unique name of the ledger. When doing a local delivery, the [ilp-connector][] reference implementation uses this segment to figure out which ledger plugin to use. As a result, it's difficult (but possible) to make a connector that directly interacts with two ledgers that use the same ledger prefix.

A ledger's prefix can be multiple segments, for example if a ledger is divided into logical or physical subledgers. If fees are necessary for connecting to a subledger, payments to that subledger must be routed through a connector, although it is not necessary for the address itself to include a connector.

If at all possible, the ledger itself should advertise what prefix(es) are used to address it. This could be reported in a metadata API method or in official communications from the ledger operator. If a ledger cannot or does not specify its prefix, whoever is running connectors to the ledger should agree upon a prefix to use. See also: [Nested Ledgers](#nested-ledgers).

[ilp-connector]: https://github.com/interledgerjs/ilp-connector


### Account Identifiers

One or more segments that serve as a unique identifier of the account within the ledger. The ledger plugin maps these to accounts within a ledger. For some ledgers, a simple conversion rule may suffice; other ledgers may require a lookup table. The [five-bells-ledger-plugin][] reference implementation translates uses one full segment exactly as the account identifier.

[five-bells-ledger-plugin]: https://github.com/interledgerjs/ilp-plugin-bells

### Interactions

Additional segments within an address. Ledgers and ledger plugins may use the interactions segment of an address when generating notifications, so programs listening for payments can respond differently based on this portion of the address. Interactions may be unique per payment or purpose.

To prevent multiple listeners from reacting to incoming payments intended for each other, the "interactions" segment of an address should start with a segment identifying how the payment was planned.


### Nested Ledgers

A ledger can be addressed relative to another _"locator"_ ledger. Smaller and lesser-known ledgers may find it easier to advertise routes to themselves in this manner. That way, rather than needing to have the ledger known to every connector in the same large neighborhood, only the connectors attached to the locator ledger need to know how to route to the smaller connector.

A connector can advertise routes to addresses that are prefixed by the connector's address in a ledger, if the connector proves it owns those addresses (for example, by sending messages using a ledger's messaging service from the account that address describes).

If `example.dev.acme.blue` is an account at ACME ledger belonging to Blue Connector, Blue Connector can advertise prefixes such as `example.dev.acme.blue.waygate.` to its peer connectors that are also on ACME ledger. This way, payments that could be routed to `example.dev.acme.blue` can also be routed to accounts in the nested WayGate ledger through Blue Connector, with ACME ledger as the locator ledger. Other connectors _could_ manually add routes that shortcut to the `example.dev.acme.blue.waygate.` ledger without going through Blue Connector or ACME ledger.

Using addresses that are nested this way depends on having a connector advertise the routes; if it doesn't, then only the manually-added "shortcut" routes can deliver money to addresses under the nested ledger prefix. Thus, it makes most sense if the connector at the locator ledger is operated by, or part of the same entity as, the nested ledger.


### Example Global Allocation Scheme Addresses

`g.acme.bob` - a destination address to the account "bob" in the ledger "acme".

`g.us-fed.ach.0.acmebank.swx0a0.acmecorp.sales.199.~ipr.cdfa5e16-e759-4ba3-88f6-8b9dc83c1868.2` - destination address for a particular invoice, which can break down as follows:

- Neighborhoods: `us-fed.`, `0.`, `ach.`
- Ledger prefixes: `acmebank.`, `swx0a0.`, `acmecorp.`
- Account identifiers: `sales`, `199`
- Interactions: `~ipr`, `cdfa5e16-e759-4ba3-88f6-8b9dc83c1868`, `2`

`g.` - the shortest possible address prefix. Includes all entries that are in the global allocation scheme.

`g.crypto.bitcoin.` - address prefix for the public Bitcoin blockchain

`g.crypto.rcl.xrp.ra5nK24KXen9AHvsdFTKHSANinZseWnPcX` - Address for sending XRP to a particular user of the Ripple Consensus Ledger, which breaks down as follows:

- Neighborhood: `crypto.`
- Ledger Prefixes: `rcl.`, `xrp.`
- Account identifier: `ra5nK24KXen9AHvsdFTKHSANinZseWnPcX`

`g.dev.ilp-blue.blue.ilp-cyan.aquahuman.~psk.6373df86-a8d1-4aaa-930d-7d5a622913bc` - Address of a particular invoice using a nested ledger, which can break down as follows:

- Neighborhood: `dev.`
- Ledger prefixes (locator ledger): `ilp-blue.`
- Connector account identifier (locator ledger): `blue.`
- Ledger prefixes (nested ledger): `ilp-cyan.`
- Account identifier (nested ledger): `aquahuman.`
- Interactions: `~psk`, `6373df86-a8d1-4aaa-930d-7d5a622913bc`
