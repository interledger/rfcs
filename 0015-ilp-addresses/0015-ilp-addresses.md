# ILP Addresses

_ILP addresses_ provide a way route payments to their intended destination through a recursive series of hops, including any number of ILP Connectors. (This happens after the payment is set up on a higher level, such as [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md).) Addresses can be subdivided into two categories:

- **Destination Addresses** are complete addresses that can receive payments. A destination address always maps to one account in a ledger. (It can also provide more specific information, such as an invoice ID or a sub-account.) Destination addresses MUST NOT end in a period (`.`) character.
- **Prefix Addresses** are incomplete addresses representing a group of destination addresses. Many depths of grouping are possible: groups of accounts or sub-accounts, an individual ledger or subledger, or entire neighborhoods of ledgers. Prefix addresses MUST end in a period (`.`) character. Payment setup protocols MUST reject payments to prefix addresses.

Both types of address usually contain one or more period characters as separators.

## Address Requirements

ILP Addresses must meet the following requirements:

1. The address MUST begin with a prefix indicating the allocation scheme. The only supported allocation scheme for now is the [General Allocation Scheme](#general-allocation-scheme), which uses the prefix `g.`.
2. Each "segment" of the address MUST contain one or more of the following characters:
    - Alphanumeric characters, upper or lower case. (Addresses are **case-sensitive** so that they can contain data encoded in formats such as base64url.)
    - Underscore (`_`)
    - Tilde (`~`)
    - Hyphen (`-`)
3. Each segment MUST be separated from other segments by a period character (`.`).
4. Prefix addresses MUST end in a period (`.`) character and MAY contain any number of segments after the allocation scheme prefix.
6. Destination addresses MUST NOT end in a period (`.`) character, and MUST contain at least two segments after the allocation scheme prefix.

The following regular expressions summarize these requirements:

| Address Type        | Regular Expression                         |
|:--------------------|:-------------------------------------------|
| All addresses       | `^g\.[a-zA-Z0-9._~-]*$`                    |
| Prefix address      | `^g\.([a-zA-Z0-9_~-]+\.)*$`                |
| Destination address | `^g\.([a-zA-Z0-9_~-]+\.)+[a-zA-Z0-9_~-]+$` |

## Example Addresses

`g.acme.bob` - a destination address to the account "bob" in the ledger "acme".

`g.us.fed.ach.0.acmebank.swx0a0.acmecorp.sales.199.cdfa5e16-e759-4ba3-88f6-8b9dc83c1868.2` - destination address for a particular invoice, which can break down as follows:

- Neighborhoods: `us`, `fed`, `ach`, `0`, `acmebank`
- Ledger: `swx0a0`
- Subledger: `acmecorp`
- Account group: `sales`
- Account: `199`
- Interactions: `cdfa5e16-e759-4ba3-88f6-8b9dc83c1868`, `2`

`g.` - the shortest possible prefix address. All entries that are in the general allocation scheme.

`g.crypto.bitcoin.` - prefix address for the public Bitcoin blockchain

## General Allocation Scheme

The general allocation scheme for ILP Addresses is currently the only supported scheme. It uses the prefix `g.`.

This scheme has no central issuing authority or mechanism, so more than one entity can use the same address. In this case, some connectors may prepare a route to a different account than intended. In this failure case, no money moves because the receiver does not send the fulfillment. Participants in the interledger can reduce the chances of encountering this failure case by choosing addresses carefully and by properly managing connectors' routing tables.

To make routing work well, we recommend including the following components as segments in an address (in order):

- [Neighborhoods](#neighborhoods)
- [Payment rail](#payment-rail)
- [Ledger prefix](#ledger-prefix)
- [Subledger and account group](#subledger-and-account-group)
- [Account identifier](#account-identifier)
- [Interactions](#interactions)


### Neighborhoods

Neighborhoods have no specific meaning, but serve as a quick shortcut for routing to the right area.

- For regional currencies, use a continent code from the folowing table:
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

### Subledger and Account Group

Zero or more segments representing optional divisions within a ledger. If there are no fees involved in transferring between a ledger and a subledger, the subledger can be a "local delivery" from the connector's perspective. If fees are necessary for connecting to a subledger, it may require a connector. ***TODO: More clarifications and detailed recommendations needed.***

### Account Identifier

A unique identifier of the account within the ledger. The ledger plugin maps these to accounts within a ledger. For some ledgers, a simple conversion rule may suffice; other ledgers may require a lookup table. ***TODO: clarify exactly how five-bells-ledger-plugin or Common Ledger API plugin do this***

### Interactions

Additional segments within an address. In most cases, any segments after the account identifier are not expected to match anything in a routing table, so they won't usually affect the routing of a payment. They may be used by automated programs listening for payments to specific purposes or situations, such as invoices.

_**Rome's note:** I'm not sure if we should say ledger plugins can use these segments to decide which account to route to or not. If they can, I'm not sure how useful it is to draw a distinction between this and the account identifier._



# Routing

_**Rome's note:** I might move this to RFC 0003 eventually._

Connectors maintain a _routing table_ of ILP addresses. Routing is a recursive lookup through the routing tables of any number of connectors. When a connector receives a query, it finds the [longest prefix match](https://en.wikipedia.org/wiki/Longest_prefix_match) for the queried address. Then, it follows one of the following cases:

- If the matching address is marked for local delivery, the connector prepares a transfer to that address in one of the ledgers connected to it. The connector's ledger plugin maps the ILP address to an account within the ledger. (This is the base case.)
- If the matching address is marked as forwarded delivery, it has the address of another connector associated with it in the routing table. The connector makes a routing lookup on the connector associated with the address. (This is the recursive case.)
