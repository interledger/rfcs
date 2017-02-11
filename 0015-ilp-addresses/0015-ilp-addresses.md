# ILP Addresses

_ILP addresses_ provide a way route payments to their intended destination through a recursive series of hops, including any number of ILP Connectors. (This happens after the payment is set up on a higher level, such as [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).) Addresses are not meant to be user-facing, but allow several ASCII characters for easy debugging.

Addresses can be subdivided into two categories:

- **Destination Addresses** are complete addresses that can receive payments. A destination address always maps to one account in a ledger. (It can also provide more specific information, such as an invoice ID or a sub-account.) Destination addresses MUST NOT end in a period (`.`) character.
- **Address Prefixes** are incomplete addresses representing a group of destination addresses. Many depths of grouping are possible: groups of accounts or sub-accounts, an individual ledger or subledger, or entire neighborhoods of ledgers. Address prefixes MUST end in a period (`.`) character. Payment setup protocols MUST reject payments to address prefixes.

Both types of address usually contain one or more period characters as separators.

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
6. Destination addresses MUST NOT end in a period (`.`) character, and MUST contain at least two segments after the allocation scheme prefix.

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
| `g.`                         | [General Allocation Scheme][] | Most ILP addresses used to send and receive real money. |
| `private.`                   | Private allocation            | For ILP addresses that only have meaning in a private subnet or intranet. Analogous to the [192.168.0.0/16 range in IPv4](https://en.wikipedia.org/wiki/Private_network). |
| `example.`                   | Examples                      | For "non-real" addresses that are used as examples or in documentation. Analogous to ["555 phone numbers"](https://en.wikipedia.org/wiki/555_%28telephone_number%29) in the USA. |
| `test1.`, `test2.`, `test3.` | Testing                       | For addresses used in tests, such as unit or integration tests of compatible software. |
| `local.`                     | Ledger-local                  | For addresses that are only valid in the context of a local ledger. Analogous to [link-local addresses](https://en.wikipedia.org/wiki/Link-local_address) in IP. |
| `peer.`                      | Peering                       | Similar to ledger-local addresses, but specifically for use in a peering relationship. The [ilp-plugin-virtual](https://github.com/interledgerjs/ilp-plugin-virtual) is an example of an existing implementation that uses this. |
| `self.`                      | Local loopback                | For addresses that are only valid on the local machine. |

## General Allocation Scheme
[General Allocation Scheme]: #general-allocation-scheme

The general allocation scheme for ILP Addresses is currently the only supported scheme. It uses the prefix `g.`.

This scheme has no central issuing authority or mechanism, so more than one entity can use the same address. In this case, some connectors may prepare a route to a different account than intended. In this failure case, no money moves because the receiver does not send the fulfillment. Participants in the interledger can reduce the chances of encountering this failure case by choosing addresses carefully and by properly managing connectors' routing tables.

The general allocation scheme does not allow you to make any assumptions about the meaning of the segments. Segments in the same place could have different meanings to different ledgers or connectors. To make routing work well, we recommend placing the segments in the following order:

- [Neighborhoods](#neighborhoods)
- [Payment rail](#payment-rail)
- [Ledger prefix](#ledger-prefix)
- [Subledger and account group](#subledger-and-account-group)
- [Account identifier](#account-identifier)
- [Interactions](#interactions)

Not all addresses contain all this information, and some addresses may use multiple segments to represent some of this information.

### Neighborhoods

Neighborhoods have no specific meaning, but serve as a quick shortcut for routing to the right area.

- For regional currencies, use a continent code from the following table:
    | Segment | Continent     |
    |:--------|:--------------|
    | `af`    | Africa        |
    | `as`    | Asia          |
    | `eu`    | Europe        |
    | `na`    | North America |
    | `sa`    | South America |
    | `oc`    | Oceania       |
    | `an`    | Antarctica    |
- For decentralized crypto-currency ledgers, use the `crypto` neighborhood.
- For naturally-ocurring commodities or other globally-distributed currencies, use the `earth` neighborhood.
- For currencies strongly associated with a particular international corporation, use the continent of that corporation's headquarters.

It may also be useful to have 1-3 levels of "sub-neighborhoods" to group together related connectors or ledgers. We have no specific recommendations at this time.

### Payment Rail

The payment rail refers to a specific way some accounts or ledgers are connected outside of ILP, such as ACH in the U.S., SEPA in Europe, or other online payment systems such as PayPal or Alipay. We recommend using an all-lowercase abbreviation for the payment rail if one is applicable to the address. Examples:

| Segment | Payment Rail                                                       |
|:--------|:-------------------------------------------------------------------|
| `ach`   | [United States Automated Clearing House](https://en.wikipedia.org/wiki/Automated_Clearing_House) |
| `sepa`  | [Single Euro Payments Area](https://en.wikipedia.org/wiki/Single_Euro_Payments_Area) |

***TODO: more rails?***

### Ledger Prefix

The ledger prefix is the unique name of the ledger. When doing a local delivery, the connector typically uses this segment to figure out which ledger plugin to use. As a result, it's difficult (but possible) to make a connector between two ledgers that use the same ledger prefix.

### Subledger

Zero or more segments representing optional divisions within a ledger; for example, if a ledger is composed of partitions that run on different hardware, the partitions could be named here. If there are no fees involved in transferring between a ledger and a subledger, this can still be a "local delivery" from the connector's perspective.

If fees are necessary for connecting to a subledger, payments to that subledger must be routed through a connector.

### Account Identifier

A unique identifier of the account within the ledger. The ledger plugin maps these to accounts within a ledger. For some ledgers, a simple conversion rule may suffice; other ledgers may require a lookup table. The five-bells-ledger-plugin reference implementation translates uses this full segment exactly as the account identifier.

If a ledger has different groupings of accounts, it might represent them as additional segments that are effectively part of the account identifier.

### Interactions

Additional segments within an address. In most cases, any segments after the account identifier are not expected to match anything in a routing table, so they won't usually affect the routing of a payment. Ledgers and ledger plugins may use the interactions segment of an address when generating notifications, so programs listening for payments can respond differently based on this portion of the address.

### Example General Allocation Scheme Addresses

`g.acme.bob` - a destination address to the account "bob" in the ledger "acme".

`g.us.fed.ach.0.acmebank.swx0a0.acmecorp.sales.199.cdfa5e16-e759-4ba3-88f6-8b9dc83c1868.2` - destination address for a particular invoice, which can break down as follows:

- Neighborhoods: `us`, `fed`, `0`
- Payment rail: `ach`
- Ledger: `acmebank`
- Subledger components: `swx0a0`, `acmecorp`
- Account components: `sales`, `199`
- Interactions: `cdfa5e16-e759-4ba3-88f6-8b9dc83c1868`, `2`

`g.` - the shortest possible address prefix. Includes all entries that are in the general allocation scheme.

`g.crypto.bitcoin.` - address prefix for the public Bitcoin blockchain

# Routing

_**Rome's note:** I might move this to RFC 0003 eventually._

Connectors maintain a _routing table_ of ILP addresses. Routing is a recursive lookup through the routing tables of any number of connectors. When a connector receives a query, it finds the [longest prefix match](https://en.wikipedia.org/wiki/Longest_prefix_match) for the queried address. Then, it follows one of the following cases:

- If the matching address is marked for local delivery, the connector prepares a transfer to that address in one of the ledgers connected to it. The connector's ledger plugin maps the ILP address to an account within the ledger. (This is the base case.)
- If the matching address is marked as forwarded delivery, it has the address of another connector associated with it in the routing table. The connector makes a routing lookup on the connector associated with the address. (This is the recursive case.)
