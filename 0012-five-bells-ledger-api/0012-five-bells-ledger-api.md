---
title: Five Bells Ledger API
draft: 1
---
# Five Bells Ledger API

The Five Bells Ledger API is a RESTful API served by a ledger (or an adapter), which provides functionality necessary for ILP compatibility. The Five Bells Ledger API provides a single standard API that a ledger can serve in order to ease integration with other Interledger Protocol components and applications, such as the reference ILP Client and ILP Connector. This is not the only way a ledger can become ILP-enabled, but it provides a template that minimizes the integration work necessary for compatibility with ILP software.

## Overview

The Five Bells Ledger API defines the following data types and structures:

- [Transfer resource][]
- [Account resource][]
- [Message resource][]
- [Crypto-Condition][] and [Crypto-Condition Fulfillment][]
- [Error Codes](#api-error-codes)

The core operations of the API are:

- [Get Ledger Metadata][]
- [Prepare Transfer][]
    - If the transfer is unconditional, it executes immediately.
    - If the transfer is conditional, it waits for a matching fulfillment.
- [Submit Fulfillment][]
    - Executes a conditional transfer, if the fulfillment matches the condition.
- [Reject Transfer][]
- [Get Transfer][] and check its status
- [Get Transfer Fulfillment][]
- [Get Account][] info including balance
- [Create or Update Account][]
- [Send Message][] to another account
- [Get Auth Token][] for [Authorization and Authentication](#authorization-and-authentication)
- [Websocket][] sub-API for subscribing to transfers and accounts

The ledger MAY support additional methods, including but not limited to:

- Health check status
- Look up transfers by account or by [Crypto-Condition][]


## Conventions

The API is designed to be [RESTful](https://en.wikipedia.org/wiki/Representational_state_transfer), extensible, and modular. By design, every resource type contains links to other methods, so you can "naturally" discover other API paths by starting from any object. Clients SHOULD NOT hardcode any [URL][] other than the path to the [Get Ledger Metadata][] method. A ledger MAY host different objects and API methods at different hostnames or base URLs, as long as all client applications can dereference the URLs in the usual way.


### JSON

All methods communicate both ways using [JavaScript Object Notation (JSON)](http://www.json.org/) unless otherwise specified. A ledger MUST use the `Content-Type: application/json` header in responses to indicate that the message body contains JSON. A ledger MAY honor the `Accept` header of the request and return the data in other formats if the client requests them. A ledger MAY interpret the message bodies of requests (PUT and POST methods) as JSON, even if the `Content-Type` header is missing or indicates a different format. The Five Bells Ledger API uses HTTP status codes to indicate the status of API operations; if the ledger encounters an error processing a request, it MUST NOT return an HTTP status code in the 200-299 range even if communication was successful.

Field names in the JSON objects defined by this API never contain literal period (`.`) characters. By convention, this documentation uses the `.` character to indicate fields nested inside other Object-type fields. In some cases, field values contain literal period (`.`) characters. Additionally, this field contains some objects that can hold arbitrary data. Arbitrary-data objects can contain any legal JSON, including field names with literal period (`.`) characters. Arbitrary-data objects SHOULD NOT contain duplicate keys.


### Amounts
[amount]: #amounts
[Amounts]: #amounts

The Five Bells Ledger API represents numeric currency amounts as strings rather than native JSON numbers. This is because many standard libraries automatically decode numbers to a [IEEE 754 double precision floating point](https://en.wikipedia.org/wiki/IEEE_floating_point) representation. Using IEEE 754 double floats can introduce a loss of precision and rounding errors that are unacceptable for financial services, depending on the range and use cases needed. (In particular, digital assets that are natively represented as 64-bit unsigned integers do not fit properly into IEEE 754 double precision floats.) Amounts in the Five Bells Ledger API MUST match the following regular expression:

`^[-+]?[0-9]*[.]?[0-9]+([eE][-+]?[0-9]+)?$`

Client applications can decode numeric strings to whatever representation provides sufficient precision for their specific needs. The ledger MUST report information about the precision it uses in the [Get Ledger Metadata][] response.


### Assets and Currency

The Five Bells Ledger API provides access to a ledger containing a single currency or asset. The [Get Ledger Metadata][] method reports the type of asset or currency used.

If a provider supports multiple currencies or assets, the provider can serve Five Bells Ledger APIs separately for each such asset by serving it from a different prefix. For example, the [Prepare Transfer][] method could be available at all the following locations:

- `POST https://ledger.example.com/TZS/transfers`
- `POST https://ledger.example.com/KES/transfers`
- `POST https://ledger.example.com/stocks/MSFT/transfers`

Any valid URL is a suitable prefix. However, only the same asset served by the same underlying ledger can be directly transferred.

These instances could be served by the same underlying software and share infrastructure, but it would not be possible to transfer directly from one to the other, since the currency denominations are different. An **ILP Connector** could facilitate cross-currency payments.

#### Adding Money to the Ledger

There are several ways to "add" money to the ledger. A ledger MAY use any or all of the following:

- When an account is created or updated by an administrator with the [Create or Update Account][] method, the administrator MAY set the balance of the account to any legal value.
- A ledger may be initialized in a state where its database contains accounts with positive balances.
- An administrator MAY create an "issuer" account whose balance can be negative. To give a positive balance to an account, execute a transfer from the issuer account. If you use this technique exclusively, the issuer account's total balance is equal to the negative of all balances in the ledger summed together.


### Scope

The Five Bells Ledger API defines one way to implement sufficient functionality to operate a ledger. It is not intended to be an optimal or ideal ledger, especially since such a thing is subjective or at least hard to quantify. (Indeed, Interledger itself was conceived from the conclusion that no one ledger can serve the needs of every person in existence.) In general, this specification reflects to the existing [Five Bells Ledger reference implementation](https://github.com/interledgerjs/five-bells-ledger) so that others may implement compatible software.


### Authorization and Authentication

The ledger MUST authenticate API clients. The RECOMMENDED method of authentication is **Token Authentication**, with tokens being served by the [Get Auth Token][] method. The Get Auth Token method SHOULD be strictly rate limited and authenticated with a secondary authentication mechanism, such as:

- [HTTP Basic Auth](https://tools.ietf.org/html/rfc2617#section-2)
- [TLS Client Certificates](https://tools.ietf.org/html/rfc5246#section-7.4.6)

The ledger MUST authenticate [WebSocket][] connections with token-based authentication.

A ledger MAY allow clients to authenticate HTTPS methods other than the Get Auth Token method using HTTP Basic Auth or TLS Client Certificates. This is NOT RECOMMENDED, especially if the ledger faces the public internet, because it makes it easier for unauthorized clients to put load on (that is, DDoS) the ledger.

The ledger MUST support authenticating a client in one of the following roles:

- Administrator - Full control over all ledger operations.
- Account owner (for a specific account) - Can perform operations relating to one specific account, such as authorizing debits from or credits to the account, and viewing the account balance.
- Unauthorized. Read-only access to some global ledger data. A ledger MUST NOT allow an unauthorized user to make a change that modifies accounts or transfers in any way.

A ledger MAY define additional authorization levels, especially for functions that extend this API.


## Data Types

### Transfer Resource
[Transfer resource]: #transfer-resource

A transfer represents money being moved around _within a single ledger_. A transfer debits one or more accounts and credits one or more accounts, such that the sum of all credits equals the sum of all debits. A transfer can be conditional upon a supplied [Crypto-Condition][], in which case it executes automatically when presented with the fulfillment for the condition. (Assuming the transfer has not expired or been rejected first.) If no Crypto-Condition is specified, the transfer is unconditional, and executes as soon as it is prepared.


A transfer object contains the fields from the following table. Some fields are _Ledger-provided_, meaning they cannot be set directly by clients. Fields that are "Optional" or "Ledger-provided" in the following table may be omitted by clients submitting transfer objects to the API, but **those fields are not optional to implement**. All fields, including the `memo` fields, must be implemented for the Five Bells Ledger API to work properly. Fields of nested objects are indicated with a dot (`.`) character; no field names contain a dot literal.

| Name                   | Type                 | Description                  |
|:-----------------------|:---------------------|:-----------------------------|
| `id`                   | [URL][]              | Client-provided ID for this resource, including a [UUID][], in the format of the [Get Transfer][] URL. MUST be unique within the ledger. See [Transfer IDs][] for more information. |
| `credits`              | Array of Objects     | Array of objects defining which accounts receive how much in this transfer. A ledger MAY restrict this to length 1. |
| `debits`               | Array of Objects     | Array of objects defining which accounts send how much in this transfer. A ledger MAY restrict this to length 1. |
| `cancellation_condition` | [Crypto-Condition][] | _(Optional)_ The condition for canceling the transfer. This field is OPTIONAL to implement. (It is no longer used by other ILP reference implementations.) MUST NOT be present unless the transfer has an `execution_condition`.  |
| `execution_condition`  | [Crypto-Condition][] | _(Optional)_ The condition for executing the transfer. If omitted, the transfer executes unconditionally. |
| `expires_at`           | [Date-Time][]        | _(Optional)_ The date when the transfer expires and can no longer be executed. |
| `additional_info`      | Object               | _(Optional)_ Arbitrary fields attached to this transfer. (For example, the IDs of related transfers in other systems.) |
| `fulfillment`          | [URL][]              | _(Ledger-provided)_ Path to the fulfillment for this transfer. MUST be an HTTP(S) URL where the client can [submit the fulfillment][Submit Fulfillment] or [get the fulfillment][Get Transfer Fulfillment]. MUST be provided if and only if this transfer has an `execution_condition`. |
| `ledger`               | [URL][]              | _(Ledger-provided)_ Resource identifier for the ledger where the transfer occurs. MUST be an HTTP(S) URL where you can [get the ledger metadata][Get Ledger Metadata]. |
| `rejection_reason`     | String               | _(Ledger-provided)_ The reason the transfer was rejected. MUST appear if and only if `state` is `rejected`. |
| `state`                | String               | _(Ledger-provided)_ The current state of the transfer. Valid states are `proposed`, `prepared`, `executed`, and `rejected`. See [Transfer States][] for more information. |
| `timeline`             | Object               | _(Ledger-provided)_ Timeline of the transfer's state transitions. |
| `timeline.executed_at` | [Date-Time][]        | _(Ledger-provided)_ Time when the transfer was originally executed. MUST appear if and only if `state` is `executed`. This time MUST be equal to or later than the `prepared_at` time. |
| `timeline.prepared_at` | [Date-Time][]        | _(Ledger-provided)_ Time when the transfer was originally prepared. MUST appear, even if the transaction is unconditional. |
| `timeline.rejected_at` | [Date-Time][]        | _(Ledger-provided)_ Time when the transfer was originally rejected. MUST appear if and only if `state` is `rejected`. This time MUST be equal to or later than the `prepared_at` time. |

[UUID]: http://en.wikipedia.org/wiki/Universally_unique_identifier

The `credits` and `debits` fields contain objects defining how much to debit or credit to a particular account. The format for the objects in both arrays is as follows:

| Field        | Type    | Description                                         |
|:-------------|:--------|:----------------------------------------------------|
| `account`    | [URL][] | An identifier for the account to credit or debit. This MUST be an HTTP(S) URL where the client can call the [Get Account][] method. |
| `amount`     | String  | Positive decimal amount of money to debit from or credit to this account. See [Amounts][] for formatting rules. |
| `memo`       | Object  | _(Optional)_ Arbitrary object with additional information about this credit or debit.  |
| `authorized` | Boolean | _(Optional, debit objects only)_ Whether this account has authorized this transfer. The ledger MUST NOT allow a request to set this value to `true` unless the client is authenticated as an Administrator or as the owner of this account. |

**Note:** Ledgers MUST implement the `memo` field. ILP clients use this field to store the ILP Packet object. Specifically, the reference ILP Client puts the ILP Packet as a base64url-encoded string in the the `ilp` field of the `memo` of the credit to the Connector. To support any possible ILP Packet, the maximum size of the `memo` field MUST be at least **46 kilobytes**.


#### Transfer IDs
[Transfer IDs]: #transfer-ids
[Transfer ID]: #transfer-ids

The transfer's `id` field is one of the main ways of identifying the transfer; it is unique across the ledger, so implementations MAY use it as a primary unique key in a database. The client applications, not the ledger, generate the `id`, so the ledger SHOULD require that the field match the proper form. If a client attempts to create a transfer with an `id` that already exists, the attempt MUST fail. (This protects clients from accidentally submitting the same transfer twice or more.)

The form for a transfer ID is the ledger's `transfer` [URL][], with a [UUID][] in canonical form as the `{id}` parameter. The UUID MUST be formatted as 32 lowercase hexadecimal digits separated by hyphens into groups of 8-4-4-4-12.

Depending on what algorithm clients use to generate UUIDs, it may be possible for other account owners to guess in advance which UUIDs might be used, and could preemptively claim `id` values that other account owners might use. A ledger MAY discourage this "squatting" behavior by imposing a limit on how many new transfers an account can generate within a fixed period of time, or with other similar limits. (A ledger could also address this issue in other ways, such as charging a fee for preparing transfers.) Client applications SHOULD use a sufficiently hard-to-predict system for generating UUIDs, such as the random algorithm described in [RFC4122](https://www.ietf.org/rfc/rfc4122). Client applications SHOULD NOT use the same ID to indicate related transfers in multiple ledgers: such behavior can be easily exploited by third parties who claim an ID in a ledger as soon as it gets used in a different ledger.

#### Transfer States
[Transfer States]: #transfer-states

The following state diagram shows the possible transitions between a transfer's `state` values:

[![Transfer state diagram](5BL-transfer-states.png)](5BL-transfer-states.png)

The [Prepare Transfer][] method creates a new transfer. Unless creator of the transfer is the only account to be debited and the account sets the `authorized` field of the debit to `true`, the transfer is created in the `proposed` state.

A transfer in the `proposed` state can be modified by other account owners calling the [Prepare Transfer][] method to set the `authorized` field to `true` for debits to their accounts.

When all a transfer's debits are authorized, the transfer executes immediately if it has no execution condition. If the transfer has an execution condition, funds from the `debits` are held and the transfer transitions to the `prepared` state.

From the `prepared` state, a transfer can be executed if an account owner calls [Submit Fulfillment][] with a fulfillment that matches the transfer's `execution_condition`. This moves the held funds to the credited accounts, fully executing the transfer and moving it to the `executed` state.

There are several ways a transfer in the `prepared` state can be rejected, which releases the funds back to the debited accounts:

- The transfer has an `expires_at` field and the time specified by that field passes
- The transfer has a `cancellation_condition` and an account owner calls [Submit Fulfillment][] with a fulfillment that matches the cancelllation condition.
- The account owner of one of the accounts to be credited calls the [Reject Transfer][] method.

The states `executed` and `rejected` are final.

### Account Resource
[Account resource]: #account-resource

An account resource contains the fields in the following table. Some fields are _Ledger-provided_, meaning they cannot be set directly by clients. Fields that are "Optional" or "Ledger-provided" in the following table may be omitted by clients submitting objects to the API, but those fields are not optional to implement. Fields of nested objects are indicated with a dot (`.`) character; no fields contain a dot literal.

An account resource usually has an owner who can [authenticate](#authorization-and-authentication) to the ledger. A ledger MUST serve all the following fields to clients authenticated as the account owner. A ledger MAY serve a subset of fields, containing at least the `name` and `id` of the account, to clients not authenticated as the account owner.

| Name                      | Type    | Description                            |
|:--------------------------|:--------|:---------------------------------------|
| `name`                    | String  | Name of the account. MUST be unique per account and MUST match the regular expression `^[a-zA-Z0-9._~-]{1,256}$`. After an account is created, this field is immutable. |
| `fingerprint`             | String  | _(Optional)_ A fingerprint of the account owner's client certificate. This field MUST be available if and only if the ledger supports client certificate authentication. MUST match the regular expression `^[0-9A-Fa-f]{2}(:[0-9A-Fa-f]{2}){19,127}$`. A ledger MAY allow the account owner to set this value. |
| `ledger`                  | [URL][] | _(Optional)_ The path to the ledger containing this account. MUST be an HTTP(S) URL where the client can [Get Ledger Metadata][]. (When an account is created, the ledger automatically provides this value.) |
| `minimum_allowed_balance` | String  | _(Optional)_ The minimum balance permitted on this account. The special value `"-infinity"` indicates no minimum balance. This is a string so that no precision is lost in JSON encoding/decoding. The default value SHOULD be `"0"`. A ledger MUST NOT allow non-administrator users to modify this value directly. |
| `is_admin`                | Boolean | _(Optional)_ If `true`, authenticating as the owner of this account gives administrator-level permissions. Only a client with administrator permissions can set this to `true`. |
| `is_disabled`             | Boolean | _(Optional)_ If `true`, this account is disabled. Defaults to `false`. Disabled accounts cannot authenticate to the API. A ledger MUST allow this to be set ONLY by administrators. |
| `balance`                 | String  | _(Optional)_ Balance as decimal [amount][]. Defaults to `"0"` at account creation. This can be negative, if the account's `minimum_allowed_balance` allows it. A ledger MAY allow clients with administrator permissions to set this value directly. A ledger MUST NOT allow non-administrator users to modify this value directly. |



### Message Resource
[Message resource]: #message-resource

Messages are sent through the ledger's [Send Message][] method and received in a [WebSocket][] subscription. All fields of the message are required:

| Field    | Value   | Description                                             |
|:---------|:--------|:--------------------------------------------------------|
| `ledger` | [URL][] | The base [URL][] of this ledger. MUST be an HTTP(S) URL where the client can [Get Ledger Metadata][]. |
| `from`   | [URL][] | Resource identifier of the account sending the message. MUST be an HTTP(S) URL where the client can [get account information][Get Account]. The sender of a message MUST be authenticated as the owner of this account. |
| `to`     | [URL][] | Resource identifier of the account receiving the message. MUST be an HTTP(S) URL where the client can [get account information][Get Account]. |
| `data`   | Object  | The message to send, containing arbitrary data. A ledger MAY set a maximum length on messages, but that limit MUST NOT be less than 510 UTF-8 characters or 2,048 bytes. |


### Crypto-Conditions
[Crypto-Condition]: #crypto-conditions
[Crypto-Condition Fulfillment]: #crypto-conditions

The [Crypto-Conditions spec](https://github.com/interledger/rfcs/tree/master/0002-crypto-conditions) defines standard formats for _conditions_ and _fulfillments_.

Conditions are distributable event descriptions, and fulfillments are cryptographically verifiable messages that prove an event occurred. If you transmit a fulfillment, then everyone who has the corresponding condition can agree that the condition has been met.

Crypto-conditions control the execution of conditional transfers. The Five Bells Ledger API supports conditions and fulfillments in string format.

The Crypto-Conditions specification anticipates that it will need to expand to keep up with changes in the field of cryptography, so conditions always define which rules and algorithms are necessary to verify the fulfillment. Implementations can use the condition's feature list to determine if they can properly process the fulfillment, without having seen the fulfillment itself.

Example condition in string format:

    cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66

Example fulfillment in string format:

    cf:0:VGhlIG9ubHkgYmFzaXMgZm9yIGdvb2QgU29jaWV0eSBpcyB1bmxpbWl0ZWQgY3JlZGl0LuKAlE9zY2FyIFdpbGRl

The [five-bells-condition](https://github.com/interledgerjs/five-bells-condition) library provides a JavaScript implementation of Crypto-Conditions. For custom implementations, consider the latest version of the [IETF crypto-conditions spec](https://tools.ietf.org/html/draft-thomas-crypto-conditions-02) as the source of truth.

**Note:** The rest of the Interledger reference implementations have dropped support for the full range of Crypto-Conditions in favor of using SHA-256 hashlocks everywhere. For compatibility with all Interledger software, Five Bells Ledger transfers should use PREIMAGE-SHA-256 crypto-conditions only.


### URLs
[URL]: #urls
[URLs]: #urls
[Metadata URL Name]: #urls
[RFC6570]: https://tools.ietf.org/html/rfc6570

The Five Bells Ledger API uses URLs as the main way of identifying and looking up resources in the API. These URLs should be formatted as valid _absolute URLs_ in accordance with the [WHATWG URL Living Standard](https://url.spec.whatwg.org/). The URLs SHOULD use the `https:` scheme, except for some [WebSocket][] paths that use the `wss:` scheme instead. In development or private subnetworks, `http:` and `ws:` are acceptable instead.

The `urls` field of the [Get Ledger Metadata][] method returns a list of paths to other API methods. Each member of the `urls` field describes one path, which MUST be an HTTP(S)-formatted URL unless otherwise specified. Some paths contain [RFC6570][]-formatted variable sections in curly braces. The `urls` field MUST include all of the following:

| Path name              | Variables | HTTP Method | API Method(s)             |
|:-----------------------|:----------|:------------|:--------------------------|
| `account`              | `{name}`  | GET         | [Get Account][], [Create or Update Account][] |
| `transfer`             | `{id}`    | GET         | [Prepare Transfer][], [Get Transfer][] |
| `transfer_fulfillment` | `{id}`    | GET, PUT    | [Get Transfer Fulfillment][], [Submit Fulfillment][] |
| `websocket`            | None      | N/A         | [WebSocket][] (MUST be a `ws://` or `wss://` URL.) |

The `urls` field of the metadata MAY also contain other methods provided by the ledger.

Some resources also contain fields whose values are URLs pointing to other methods. These URLs MUST NOT contain [RFC6570][]-formatted variable sections. The following table maps URL fields to the API methods that can be accessed at those paths:

| Resource | Field                            | HTTP Method | API Method       |
|:---------|:---------------------------------|:------------|:-----------------|
| Transfer | `ledger` field                   | GET         | [Get Ledger Metadata][] |
| Transfer | `credits` member `account` field | GET         | [Get Account][]  |
| Transfer | `debits` member `account` field  | GET         | [Get Account][]  |
| Message  | `from` field                     | GET         | [Get Account][]  |
| Message  | `to` field                       | GET         | [Get Account][]  |
| Message  | `ledger` field                   | GET         | [Get Ledger Metadata][] |


### Date-Time
[Date-Time]: #date-time

All dates and times should be expressed in [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) date-time format with precision to the second or millisecond. The time zone offset should always be `Z`, for no offset. In other words, the date-time should be a **string** matching the one of the following formats:

| Precision   | Format                     |
|:------------|:---------------------------|
| Second      | `YYYY-MM-DDTHH:mm:ssZ`     |
| Millisecond | `YYYY-MM-DDTHH:mm:ss.sssZ` |


## API Methods

### Get Ledger Metadata
[Get Ledger Metadata]: #get-ledger-metadata

Receive information about the ledger.

**Authorization:** This method MUST be accessible to all clients authorized as account owners or administrators. This method MAY be accessible to unauthorized users.

#### Request Format

```
GET /
```

**[Metadata URL Name][]:** None (top-level path for the ledger)

##### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON object with the following fields. (A field name like `foo[].bar` indicates that the row describes the field `bar` in _each_ object contained in the array `foo`.)

| Field             | Value     | Description                                  |
|:------------------|:----------|:---------------------------------------------|
| `currency_code`   | String    | Three-letter ([ISO 4217](http://www.xe.com/iso4217.php)) code of the currency this ledger tracks. |
| `currency_symbol` | String    | Currency symbol to use in user interfaces for the currency represented in this ledger. For example, "$". |
| `ilp_prefix`      | String    | The ILP Address Prefix of the ledger. This must match the definition from [IL-RFC-15: ILP Addresses](https://github.com/interledger/rfcs/blob/master/0015-ilp-addresses/0015-ilp-addresses.md). |
| `connectors`      | Array     | Array of _recommended_ ILP Connectors. Each member of this list MUST be an object with two fields, as described below. This list MAY be empty. |
| `precision`       | Integer   | How many total decimal digits of precision this ledger uses to represent currency amounts. |
| `scale`           | Integer   | How many digits after the decimal place this ledger supports in currency amounts. |
| `urls`            | Object    | Paths to other methods exposed by this ledger. Each field name is short name for a method and the value is the path to that method. Some fields MUST be present; see [URLs][] for details. |
| `rounding`        | String    | _(Optional)_ The type of rounding used internally by ledger for values that exceed the reported `scale` or `precision`. If provided, the value MUST be `floor`, `ceiling`, or `nearest`. |
| ...               | (Various) | _(Optional)_ Additional arbitrary values as desired. |

Each member of the `connectors` array MUST have the following fields:

| Field  | Value   | Description                                               |
|:-------|:--------|:----------------------------------------------------------|
| `id`   | [URL][] | HTTP(S) URL where a client can [get the connector's account at this ledger][Get Account]. |
| `name` | String  | The connector's unique username in this ledger.           |

#### Example

Request:

```
GET /
```

Response:

```json
HTTP/1.1 200 OK

{
  "currency_code": "EUR",
  "currency_symbol": "€",
  "connectors": [{
    "id": "https://red.ilpdemo.org/ledger/accounts/connie",
    "name": "connie"
  }],
  "urls": {
    "health": "https://red.ilpdemo.org/ledger/health",
    "transfer": "https://red.ilpdemo.org/ledger/transfers/{id}",
    "transfer_fulfillment": "https://red.ilpdemo.org/ledger/transfers/{id}/fulfillment",
    "account": "https://red.ilpdemo.org/ledger/accounts/{name}",
    "websocket": "wss://red.ilpdemo.org/ledger/websocket/"
  },
  "precision": 10,
  "scale": 2
}
```


#### Errors

- This method does not return any errors under normal circumstances.


### Prepare Transfer
[Prepare Transfer]: #prepare-transfer

Prepares a new transfer (conditional or unconditional) in the ledger, or updates an existing transfer. If updating an existing transfer, only the `authorized` field of a debit can be changed. Only the owner of a particular account may set the `authorized` field of a debit to that account.

An unconditional transfer executes automatically as soon as all debits are authorized. A conditional transfer holds the debited funds until it is executed by the [Submit Fulfillment][] method or it is rejected. See [Transfer States][] for more information.

A ledger SHOULD reject a request to create a `proposed` transfer, unless the client is authenticated as one of the accounts in the `debits` or `credits` of the transfer, or the client is authenticated as an administrator.

**Authorization:** The owner of an account MUST be able to prepare a conditional transfer that debits the account. Non-administrators MUST NOT be able to prepare a transfer that debits a different account. A ledger MAY disallow non-administrators from preparing unconditional transfers.

#### Request Format

```
PUT /transfers/{id}
```

**[Metadata URL Name][]:** `transfer`

##### URL Parameters

| Field | Value   | Description                                               |
|:------|:--------|:----------------------------------------------------------|
| `id`  | [URL][] | A new [Transfer ID][] URL, including a [UUID][]. |

##### Body Parameters

The message body should be a JSON [Transfer resource][].

#### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON body with the [Transfer resource][] as saved.

#### Example

Request:

```json
PUT /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204
Content-Type: application/json

{
  "id": "https://red.ilpdemo.org/ledger/transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204",
  "debits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/alice",
    "amount": "50",
    "authorized": true
  }],
  "credits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/bob",
    "amount": "50"
  }],
  "execution_condition": "cc:0:3:8ZdpKBDUV-KX_OnFZTsCWB_5mlCFI3DynX5f5H2dN-Y:2",
  "expires_at": "2015-06-16T00:00:01.000Z"
}
```

Response:

```json
HTTP/1.1 200 OK


{
  "id": "https://red.ilpdemo.org/ledger/transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204",
  "ledger": "https://red.ilpdemo.org/ledger/",
  "debits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/alice",
    "amount": "50",
    "authorized": true
  }],
  "credits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/bob",
    "amount": "50"
  }],
  "execution_condition": "cc:0:3:8ZdpKBDUV-KX_OnFZTsCWB_5mlCFI3DynX5f5H2dN-Y:2",
  "expires_at": "2015-06-16T00:00:01.000Z",
  "state": "prepared",
  "timeline": {
    "prepared_at": "2015-06-15T10:33:01.461Z"
  }
}
```

#### Errors

- [InsufficientFundsError][] - A debited account would go below its `minimum_allowed_balance` if this transfer were executed
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem.
- [AlreadyExistsError][] - The `id` supplied is already used by another transfer.
- [InvalidUriParameterError][] - One of the [URL][] or [UUID][] parameters was not formatted properly.
- [InvalidBodyError][] - The request body was not properly-formatted JSON, did not match the Content-Type provided, or did not match the schema for the requested resource type.
- [UnsupportedCryptoConditionError][] - The transfer included an `execution_condition` whose feature bitstring requires functionality not implemented by this ledger.


### Submit Fulfillment
[Submit Fulfillment]: #submit-fulfillment

Execute or cancel a transfer by submitting a [Crypto-Condition Fulfillment][].

To execute a transfer, the transfer MUST begin in the `prepared` state and the submitted fulfillment must satisfy the [Crypto-Condition][] in the transfer's `execution_condition` field. Doing so transitions the transaction to `executed`.

To cancel a transfer, the submitted fulfillment must satisfy the [Crypto-Condition][] in the transfer's `cancellation_condition` field. Doing so transitions the transaction to `rejected`.

**Authorization:** The owner of an account MUST be able to submit the fulfillment for a transfer that credits the account. A ledger MAY allow other account owners or unauthorized clients to submit a fulfillment.

#### Request Format


```
PUT /transfers/{id}/fulfillment
Content-Type: text/plain
```

**Caution:** This method requires the request to specify the header `Content-Type: text/plain`

**[Metadata URL Name][]:** `transfer_fulfillment`.

##### Body Parameters

The message body should be a [Crypto-Condition Fulfillment][] in string format.

#### Response Format

A successful result uses the HTTP response code **200 OK**. The message body of the response is the submitted fulfillment as plain text. A ledger MUST return a successful response if and only if the transfer was executed or canceled as a result of this request.

#### Example

Request:

```
PUT /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/fulfillment
Content-Type: text/plain

cf:0:_v8
```

Response:

```
HTTP/1.1 200 OK

cf:0:_v8
```

#### Errors

- [NotFoundError][] - The transfer does not exist.
- [UnmetConditionError][] - The fulfillment does not match the condition.
- [TransferNotConditionalError][] - The transfer had no condition to fulfill.
- [TransferStateError][] - The transfer was not in the `prepared` state when the request was received. See [Transfer States][] for more information.
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem.
- [InvalidBodyError][] - The request body was not properly-formatted JSON, or did not match the schema for the request.


### Reject Transfer
[Reject Transfer]: #reject-transfer

Reject a prepared transfer. A transfer can be rejected if and only if that transfer is in the `prepared` state. Doing so transitions the transfer to the `rejected` state.

**Authorization:** Accounts from the `credits` field of a transfer MUST be able to reject the transfer. Any other non-admin user MUST NOT be able to reject the transfer.

#### Request Format

```
PUT /transfers/{id}/rejection
Content-Type: text/plain

your rejection reason here
```

**[Metadata URL Name][]:** `transfer_rejection`.

This request MUST use the header `Content-Type: text/plain`.

##### Body Parameters

The message body contains the rejection reason as plain text. The rejection reason is an arbitrary string that is intended to be a machine-readable identifier indicating the reason for the transfer's rejection. This string should be no more than 2KB or 512 UTF-8 characters.

#### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON object containing the updated [Transfer resource][] containing the rejection reason.

#### Example

Request:

```json
PUT /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/rejection
Content-Type: text/plain

BlacklistedSender
```

Response:

```json
HTTP/1.1 200 OK

{
  "ledger": "https://red.ilpdemo.org/ledger",
  "id": "63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "debits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/alice",
    "amount": "50",
    "authorized": true
  }],
  "credits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/bob",
    "amount": "50"
  }],
  "amount": "199.99",
  "execution_condition": "cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66",
  "expires_at": "2018-01-01T00:00:00.000Z",
  "state": "rejected",
  "timeline": {
    "prepared_at": "2016-10-21T22:45:01.000Z",
    "rejected_at": "2016-10-22T21:33:34.867Z"
  },
  "rejection_reason": "BlacklistedSender"
}
```

#### Errors

- [NotFoundError][] - The transfer does not exist.
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem. This includes cases where the transfer has already been executed or rejected.
- [InvalidBodyError][] - The request's message body was too long or the request did not use the proper Content-Type header (text/plain).
- [TransferStateError][] - The transfer was not in the `prepared` state when the request was received. See [Transfer States][] for more information.


### Get Transfer
[Get Transfer]: #get-transfer

Check the details or status of a local transfer.

**Authorization:** The accounts from the `credits` and `debits` field of a transfer MUST be able to get that transfer. A ledger MAY allow other account owners or unauthorized clients to get a transfer.

#### Request Format

```
GET /transfers/{id}
```

**[Metadata URL Name][]:** `transfer`. Suggested generic path: `/transfers/{id}`

#### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON body with the requested [Transfer resource][].

#### Example

Request:

```
GET /transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf
```

Response:

```json
HTTP/1.1 200 OK

{
  "ledger": "https://red.ilpdemo.org/ledger",
  "id": "63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "debits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/alice",
    "amount": "50",
    "authorized": true
  }],
  "credits": [{
    "account": "https://red.ilpdemo.org/ledger/accounts/bob",
    "amount": "50"
  }],
  "amount": "199.99",
  "execution_condition": "cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66",
  "expires_at": "2018-01-01T00:00:00.000Z",
  "state": "rejected",
  "timeline": {
    "prepared_at": "2016-10-21T22:45:01.000Z",
    "rejected_at": "2016-10-22T21:33:34.867Z"
  },
  "rejection_reason": "BlacklistedSender"
}
```

#### Errors

- [NotFoundError][] - No transfer with a matching ID was found.
- [InvalidUriParameterError][] - The transfer ID from the request was not a valid [UUID][].


### Get Transfer Fulfillment
[Get Transfer Fulfillment]: #get-transfer-fulfillment

Retrieve the fulfillment for a transfer that has been executed or rejected. This is separate from the [Transfer resource][] because it can be very large.

**Authorization:** The ledger MUST allow account owners from the account's `debits` and `credits` to get the transfer's fulfillment. A ledger MAY allow other account owners or unauthorized users to get a transfer's fulfillment.

#### Request Format

```
GET /transfers/{id}/fulfillment
```

**[Metadata URL Name][]:** `transfer_fulfillment`.

##### URL Parameters

| Field | Value | Description                                                 |
|:------|:------|:------------------------------------------------------------|
| `id`  | UUID  | The [UUID][] of the Transfer whose fulfillment to retrieve. |

#### Response Format

A successful result uses the HTTP response code **200 OK** and the header `Content-Type: text/plain`. The body contains the Transfer's [Crypto-Condition Fulfillment][] in text format.

#### Example

Request:

```
GET /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/fulfillment
```

Response:

```
HTTP/1.1 200 OK
Content-Type: text/plain

cf:0:_v8
```

#### Errors

- [NotFoundError][] - The specified transfer does not exist,
- [InvalidUriParameterError][]


### Get Account
[Get Account]: #get-account

Get an account resource.

**Authorization:** The owner of an account MUST be able to get the account resource. A ledger MAY allow other account owners or unauthorized users to get other account resources. A ledger MAY return a subset of fields when it returns an account resource to any client other than the account owner (for example, omitting the balance).

#### Request Format

```
GET /accounts/{name}
```

**[Metadata URL Name][]:** `account`.

#### Response Format

A successful response uses the HTTP response code **200 OK** and contains the [Account resource][] in JSON format.

#### Example

Request:

```
GET /accounts/bob
```

Response:

```json
HTTP/1.1 200 OK
Content-Type: application/json

{
  "id": "https://red.ilpdemo.org/ledger/accounts/bob",
  "name": "bob",
  "balance": "5007734.0",
  "ledger": "https://red.ilpdemo.org/ledger",
  "fingerprint": "88:90:3a:e7:e5:1c:c4:51:05:4b:0c:2b:3f:41:df:bf:0c:21:f3:78",
  "minimum_allowed_balance": "-infinity"
}
```

#### Errors

- [NotFoundError][]
- [InvalidUriParameterError][]


### Create or Update Account
[Create or Update Account]: #create-or-update-account

Update an account in the ledger.

**Authorization:** The owner of an account MUST be able to update the account, except for specific fields. An administrator MAY be able to update any fields of any account.

#### Request Format

```
PUT /accounts/{name}
```

**[Metadata URL Name][]:** `account`.

##### URL Parameters

| Field  | Type   | Description                                                |
|:-------|:-------|:-----------------------------------------------------------|
| `name` | String | The unique name of the account to create or update. MUST match the regular expression `^[a-zA-Z0-9._~-]{1,256}$`. |

##### Request Body

The request is an [Account Resource][]. Any omitted fields are left unchanged.

#### Response Format

A successful response uses the HTTP status code **200 OK** and contains a JSON object with the [Account Resource][] as saved.

#### Example

Request:

```
PUT /accounts/bob
Content-Type: application/json

{
  "name": "bob",
  "minimum_allowed_balance": "-10000",
  "fingerprint": "88:90:3a:e7:e5:1c:c4:51:05:4b:0c:2b:3f:41:df:bf:0c:21:f3:78"
}
```

Response:

```
200 OK
Content-Type: application/json

{
  "name": "bob",
  "minimum_allowed_balance": "-10000",
  "ledger": "https://red.ilpdemo.org/ledger",
  "is_disabled": false,
  "fingerprint": "88:90:3a:e7:e5:1c:c4:51:05:4b:0c:2b:3f:41:df:bf:0c:21:f3:78"
}
```

#### Errors

- [InvalidBodyError][] - The request was not valid JSON, or did not match the schema for the request.
- [InvalidUriParameterError][] - One of the URLs, URIs, or UUIDs in the body is not validly formatted.
- [UnprocessableEntityError][] - The object was syntactically valid but had a semantic issue.
- [UnauthorizedError][] - The client was not authenticated with permissions to modify the account as requested.




### Send Message
[Send Message]: #send-message

Try to send a notification to another account. The message is only delivered if the other account is subscribed to [account notifications](#subscribe-to-account) on a WebSocket connection. ILP Clients and ILP Connectors use this method to request and send quotes.

**Authorization:** The `from` field of the message MUST match the account owner. Unauthenticated users MUST NOT be able to send messages. A ledger MAY allow admin connections to send messages whose `from` value matches the ledger's base [URL][].

#### Request Format

```
POST /messages
```

**[Metadata URL Name][]:** `message`.

The request body contains a [Message object][] as JSON.

#### Response Format

A successful response uses the HTTP response code **201 Created** and contains no message body or an empty message body.

#### Example

Request:

```json
POST /messages
Content-Type: application/json

{
  "from": "https://blue.ilpdemo.ripple.com/ledger/accounts/bob",
  "to": "https://blue.ilpdemo.ripple.com/ledger/accounts/alice",
  "data": {
    "method": "quote_request",
    "id": "721e4126-98a1-4974-b35a-8a8f4655f934",
    "data": {
      "source_amount": "100.25",
      "source_address": "example.eur-ledger.alice",
      "destination_address": "example.usd-ledger.bob",
      "source_expiry_duration": "6000",
      "destination_expiry_duration": "5"
    }
  }
}
```

Response:

```
HTTP/1.1 204 No Content
```

#### Errors

- [InvalidBodyError][] - The request was not valid JSON, or did not match the schema for the request.
- [InvalidUriParameterError][] - One of the URLs, URIs, or UUIDs in the body is not validly formatted.
- [UnprocessableEntityError][] - The object was syntactically valid but had a semantic issue.


### Get Auth Token
[Get Auth Token]: #get-auth-token

Get a token that can be used to authenticate future requests.

**Note:** This method is REQUIRED for ledgers to authenticate [WebSocket][] connections. If the ledger does not authenticate WebSocket connections, this method is OPTIONAL. The ledger MAY allow clients to authenticate for any other methods of the API using the tokens returned by this method.

#### Request Format

```
GET /auth_token
```

Depending on the [authentication mechanism](#authorization-and-authentication) used by this ledger, the ledger MAY require the HTTP `Auth` header with a valid username and password, or the ledger may require a different method of authentication.

**[Metadata URL Name][]:** `auth_token`.

#### Response Format

A successful response uses the HTTP response code **200 OK** and contains a JSON object with a token that can be used for subsequent requests. The ledger can generate the token with [JWT](https://jwt.io/) or any similar system.

#### Example

Request:

```
GET /auth_token
Authorization: Basic myUsername:securePassphrase
```

Response:

```json
HTTP/1.1 200 OK
Content-Type: application/json

{
  "token": "9AtVZPN3t49Kx07stO813UHXv6pcES"
}
```

#### Errors

- [Unauthorized][]
- [Forbidden][]



## WebSocket
[WebSocket]: #websocket

**[Metadata URL Name][]:** `websocket`. Suggested generic path: `/websocket` (with `wss://` protocol)

Clients can subscribe to live, read-only notifications of ledger activity by opening a [WebSocket](https://developer.mozilla.org/en-US/docs/Web/API/WebSockets_API) connection to this path and sending a subscription request.

### WebSocket Authentication

Clients MUST authenticate themselves with a token from the [Get Auth Token][] method. This token can be supplied in one of two ways:

- In the `token` query parameter. For example:

        wss://red.ilpdemo.org/ledger/websocket/?token=9AtVZPN3t49Kx07stO813UHXv6pcES

- As a "Bearer" token in the `Authorization` HTTP header of the request (before the protocol switch to WebSocket). For example:

        GET /ledger/websocket
        Authorization: Bearer 9AtVZPN3t49Kx07stO813UHXv6pcES
        Upgrade: websocket

Clients should prefer to use the `Authorization` header on WebSocket requests, if the client supports it.

A ledger MAY restrict the data that can be accessed, as long as it complies with the following rules:

- An account owner MUST be able to subscribe to changes to its own account.
- An account owner MUST be able to subscribe to changes to transactions where the account is the in the `credits` or `debits` fields.
- An account owner MUST be able to subscribe to messages to its account. Account owners and unauthorized users MUST NOT be able to subscribe to messages to other accounts.

The authentication you use when opening the connection applies to all subscriptions made in the connection.

A ledger MUST support multiple independent WebSocket connections with the same authentication. (This provides connection redundancy for notifications, which is helpful for ILP Connectors.)

### WebSocket Messages

After the connection is established, the client and ledger communicate by passing [JSON-RPC 2.0](http://www.jsonrpc.org/specification) messages back and forth. Both the client application and ledger can take the roles of "client" and "server" in JSON-RPC terms. The client application can submit requests to subscribe or unsubscribe from specific categories of message. The ledger responds directly to the client's requests with confirmation messages, and also sends "notification" requests to the client application. (Notifications are identified by the `id` value `null`.)

A ledger MUST support the following subscription command:

- [Subscribe to Account](#subscribe-to-account)

A ledger MAY support the following subscription commands, or define additional subscription commands:

- [Subscribe to Transfer](#subscribe-to-transfer)
- Subscribe to All Transfers
    - This is useful when you have an application monitoring activity on all accounts and fulfilling transfers for others.

#### Subscribe to Account

This request replaces any existing account subscriptions on this WebSocket connection. The client sends a JSON object to the ledger with the following fields:

| Field              | Value            | Description                          |
|:-------------------|:-----------------|:-------------------------------------|
| `id`               | String or Number | An arbitrary identifier for this request. MUST NOT be `null`. The immediate response to this request identifies itself using the same `id`. |
| `jsonrpc`          | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 request. |
| `method`           | String           | MUST be the value `"subscribe_account"`. |
| `params`           | Object           | Information on what subscriptions to open. |
| `params.accounts`  | Array            | Each member of this array must be the [URI][] of an account to subscribe to, as a string. This replaces existing subscriptions; if the array length is zero, the client is unsubscribed from all account notifications. |

##### Response
The ledger acknowledges the request immediately by sending a JSON object with the following fields:

| Field     | Value            | Description                                   |
|:----------|:-----------------|:----------------------------------------------|
| `id`      | String or Number | The `id` value from the request. This helps distinguish responses from other messages. |
| `jsonrpc` | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 message. |
| `result`  | Number           | Updated number of active account subscriptions on this WebSocket connection. In practice, this is usually the length of the `params.accounts` array from the request. |

Later, the ledger responds with [notifications](#websocket-notifications) whenever any of the following occurs:

- A transfer affecting the account is prepared (`event` type: `transfer.create`)
- A transfer affecting the account changes state. For example, from prepared to executed or to expired. (`event` type: `transfer.update`)
- Someone [sends a message](#send-message) to the account. (`event` type: `message.send`)
- A ledger MAY define additional types of notifications that get sent when you are subscribed to an account. Each new type of notification MUST have a unique `event` value.

Example:

```
--> {
      "jsonrpc": "2.0",
      "method": "subscribe_account",
      "params": {
        "accounts": ["https://ledger.example/accounts/alice"]
      },
      "id": 1
    }
<-- {
      "jsonrpc": "2.0",
      "result": 1,
      "id": 1
    }
```


#### Subscribe to Transfer

The client sends a JSON object to the ledger with the following fields:

| Field              | Value            | Description                          |
|:-------------------|:-----------------|:-------------------------------------|
| `id`               | String or Number | An arbitrary identifier for this request. MUST NOT be `null`. |
| `jsonrpc`          | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 request. |
| `method`           | String           | MUST be the value `"subscribe_transfer"`. |
| `params`           | Object           | Information on what subscriptions to open. |
| `params.transfers` | Array            | Each member of this array must be the [URL][] of a transfer to subscribe to, as a string. This array replaces any existing transfer subscriptions on this WebSocket connection. If the array length is zero, the client is unsubscribed from all transfer notifications. |

##### Response
The ledger acknowledges the request immediately by sending a JSON object with the following fields:

| Field     | Value            | Description                                   |
|:----------|:-----------------|:----------------------------------------------|
| `id`      | String or Number | The `id` value from the request. This helps distinguish responses from other messages. |
| `jsonrpc` | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 request. |
| `result`  | Number           | Updated number of active transfer subscriptions on this WebSocket connection. In practice, this is usually the length of the `params.transfers` array from the request. |

Later, the ledger responds with [notifications](#websocket-notifications) whenever any of the following occurs:

- The transfer changes state. For example, from prepared to executed or to expired. (`event` type: `transfer.update`)


#### WebSocket Notifications

The ledger sends notifications to connected clients when certain events occur, according to the current subscriptions of the clients. Every notification is sent at most once per WebSocket connection to the ledger, even if a client is subscribed to multiple categories of message that should prompt the same notification. If a client has multiple connections open, the ledger MUST attempt to send a message on every open connection.

All event notifications from the ledger are in the format of JSON objects with the following fields:

| Field                      | Value   | Description                           |
|:---------------------------|:--------|:--------------------------------------|
| `jsonrpc`                  | String  | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 notification. |
| `id`                       | Null    | MUST be `null` to indicate a notification. |
| `method`                   | String  | MUST be the value `"notify"`          |
| `params`                   | Object  | Nested object with information about the notification. |
| `params.event`             | String  | The type of event that prompted this notification. Valid types include `transfer.create`, `transfer.update`, and others. See [Event Types](#event-types) for more information. |
| `params.id`                | [URL][] | _(Optional)_ A [UUID][] to uniquely identify this notification. |
| `params.resource`          | Object  | An object related to `event` that occurred. In most cases, this is a [Transfer resource][] as it was created or updated. |
| `params.related_resources` | Object  | _(Not present in all responses)_ Contains additional resources related to this notification in named sub-fields, depending on the `event` type. In particular, this MUST contain the fulfillment when a transfer is updated to the `executed` state. |

##### Event Types
[Event Types]: #event-types

A ledger MAY define custom `event` types. A ledger MUST support at least the following `event` values:

| Value             | Resource              | Description                      |
|:------------------|:----------------------|:---------------------------------|
| `transfer.create` | [Transfer resource][] | Occurs when a new transfer is prepared. Sent to clients subscribed to the accounts from the `debits` and `credits` fields of the transfer. If the transfer is unconditional, this notification indicates the state of the transaction after execution. The `related_resources` field is omitted. |
| `transfer.update` | [Transfer resource][] | Occurs when a transfer changes state from `prepared` to `executed` or `rejected`. If the transfer was executed, the `execution_condition_fulfillment` field of `related_resources` MUST contain the fulfillment. If the transfer was rejected, the `related_resources` field is empty. |
| `message.send`    | [Message resource][]  | Occurs when someone else sends a message. |

If a ledger creates custom event types, their values should follow the convention `{resource}.{event}`.


## API Error Codes

The Five Bells Ledger API may return errors using HTTP codes in the range 400-599, depending on the type of error. The message body of the error response is a JSON object with additional information about the nature of the error.

Every error response contains at least the following fields:

| Field     | Type   | Description                                             |
|:----------|:-------|:--------------------------------------------------------|
| `id`      | String | A unique error code for this specific type of error, such as `UnmetConditionError`. |
| `message` | String | A longer, human-readable description for the cause of the error. |

Errors may also have additional arbitrary fields describing the cause or context of the error.

**Note:** Any fields other than `id` and `message` should be considered optional and informational. Clients MUST NOT depend on the presence of those fields. The examples in this spec contain suggestions for additional fields, but those should not be taken as requirements.

### Unauthorized
[Unauthorized]: #unauthorized

The [authentication information](#authorization-and-authentication) supplied to this request was insufficient for one of the following reasons:

- This method requires authentication but none was provided
- The credentials were provided using a system not supported by this method. (For example, using Basic Auth on a method that requires token authentication.)

A ledger MAY return any message body using any content type with this error. (This makes it easier to use proxy servers and stock server configuration to handle authorization.)

**HTTP Status Code:** 401 Unauthorized

```json
HTTP/1.1 401 Unauthorized

{
  "error_id": "Unauthorized",
  "message": "Auth token not found"
}
```


### Forbidden
[Forbidden]: #forbidden

The request provided

- The credentials were malformed or don't match the known account information
- The authenticated role does not have permission to perform the requested operation

A ledger MAY return any message body using any content type with this error. (This makes it easier to use proxy servers and stock server configuration to handle authorization.)

**HTTP Status Code:** 403 Forbidden

```json
HTTP/1.1 403 Forbidden

{
  "error_id": "Forbidden",
  "message": "Client certificate doesn't match known fingerprint"
}
```

### InvalidUriParameterError
[InvalidUriParameterError]: #invaliduriparametererror

At least one provided [URL][] or [UUID][] parameter was invalid.

**HTTP Status Code:** 400 Bad Request

```json
HTTP/1.1 400 Bad Request

{
	"error_id": "InvalidUriParameterError",
	"message": "id is not a valid Uuid",
	"validationErrors": [{
		"message": "String does not match pattern: ^[a-fA-F0-9]{8}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{12}$",
		"params": {
			"pattern": "^[a-fA-F0-9]{8}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{12}$"
		},
		"code": 202,
		"dataPath": "",
		"schemaPath": "/pattern",
		"subErrors": null,
        "stack": "..."
    }]
}
```


### InvalidBodyError
[InvalidBodyError]: #invalidbodyerror

The submitted JSON entity does not match the required schema.

**HTTP Status Code:** 400 Bad Request

```json
HTTP/1.1 400 Bad Request

{
	"error_id": "InvalidBodyError",
	"message": "Body did not match schema Transfer",
	"validationErrors": [{
		"message": "Missing required property: id",
		"params": {
			"key": "id"
		},
		"code": 302,
		"dataPath": "",
		"schemaPath": "/required/0",
		"subErrors": null,
		"stack": "..."
	}]
}
```

### NotFoundError
[NotFoundError]: #notfounderror

The requested resource could not be found.

**HTTP Status Code:** 404 Not Found

```json
HTTP/1.1 404 Not Found

{
  "error_id": "NotFoundError",
  "message": "Unknown transfer."
}
```

### UnprocessableEntityError
[UnprocessableEntityError]: #unprocessableentityerror

The provided entity is syntactically correct, but there is a generic semantic problem with it.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "UnprocessableEntityError",
  "message": "Debits and credits are not equal"
}
```

### InsufficientFundsError
[InsufficientFundsError]: #insufficientfundserror

The source account does not have sufficient funds to satisfy the request.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "InsufficientFundsError",
  "message": "Sender has insufficient funds.",
  "account": "santiago"
}
```

### AlreadyExistsError
[AlreadyExistsError]: #alreadyexistserror

The specified entity already exists and may not be modified.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "AlreadyExistsError",
  "message": "Can't modify transfer after execution."
}
```

### UnauthorizedError
[UnauthorizedError]: #unauthorizederror

You do not have permissions to access or modify this resource in the requested way.

**HTTP Status Code:** 403 Forbidden

```json
HTTP/1.1 403 Forbidden

{
  "error_id": "UnauthorizedError",
  "message": "Only the beneficiary can post the fulfillment."
}
```

### UnmetConditionError
[UnmetConditionError]: #unmetconditionerror

The submitted fulfillment does not meet the specified [Crypto-Condition][].

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "UnmetConditionError",
  "message": "Fulfillment does not match condition.",
  "condition": "cc:2:2b:mJUaGKCuF5n-3tfXM2U81VYtHbX-N8MP6kz8R-ASwNQ:146",
  "fulfillment": "cf:1:DUhlbGxvIFdvcmxkISAABGDsFyuTrV5WO_STLHDhJFA0w1Rn7y79TWTr-BloNGfiv7YikfrZQy-PKYucSkiV2-KT9v_aGmja3wzN719HoMchKl_qPNqXo_TAPqny6Kwc7IalHUUhJ6vboJ0bbzMcBwo"
}
```

### TransferNotConditionalError
[TransferNotConditionalError]: #transfernotconditionalerror

Occurs when a client tries to submit a fulfillment to a transfer that does not have a [Crypto-Condition][] to fulfill.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "TransferNotConditionalError",
  "message": "Transfer does not have a condition.",
  "transfer_id": "da405506-0fbe-4454-9b6f-c413977a7f3c"
}
```

### UnsupportedCryptoConditionError
[UnsupportedCryptoConditionError]: #unsupportedcryptoconditionerror

The transfer uses a [Crypto-Condition][] with features not supported by this ledger's implementation of Crypto-Conditions.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "UnsupportedCryptoConditionError",
  "message": "Ledger does not support this CryptoCondition type.",
  "condition": "cc:2:2b:mJUaGKCuF5n-3tfXM2U81VYtHbX-N8MP6kz8R-ASwNQ:146",
}
```



### TransferStateError
[TransferStateError]: #transferstateerror

The requested operation could not be executed because the transfer was not in the correct state when the request was received. This occurs if you try to execute or reject a transfer that has already been executed, rejected, or expired.

**HTTP Status Code:** 422 Unprocessable Entity

```json
HTTP/1.1 422 Unprocessable Entity

{
  "error_id": "TransferStateError",
  "message": "Transfer 3f1080b4-b296-4de5-8a16-55362ee0624f expired 594726 seconds ago",
  "expires_at": "2016-10-25T08:41:59.795Z",
  "current_time": "2016-10-25T08:51:54.521Z",
  "transfer_id": "3f1080b4-b296-4de5-8a16-55362ee0624f"
}
```
