# Common Ledger API

The Common Ledger API is a RESTful API served by a ledger (or an adapter), which provides functionality necessary for ILP compatibility. The Common Ledger API provides a single standard API that a ledger can serve in order to ease integration with other Interledger Protocol components and applications, such as the reference ILP Client and ILP Connector. This is not the only way a ledger can become ILP-enabled, but it provides a template that minimizes the integration work necessary for compatibility with ILP software.

## Overview

The Common Ledger API defines the following data types and structures:

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
    - Can execute or cancel the transfer, depending on the fulfillment.
- [Reject Transfer][]
- [Get Transfer][] and check its status
- [Get Transfer Fulfillment][]
- [Get Account][] info including balance
- [Send Message][] to another account
- [Get Auth Token][] for [Authorization and Authentication](#authorization-and-authentication)
- [Websocket][] sub-API for subscribing to transfers and accounts

The ledger MAY support additional methods, including but not limited to:

- Create or Update Account
- Health check status
- Look up transfers by account or [Crypto-Condition][]


## Conventions

The API is designed to be [RESTful](https://en.wikipedia.org/wiki/Representational_state_transfer), extensible, and modular. By design, every resource type contains links to other methods, so you can "naturally" discover other API paths by starting from any object. Clients SHOULD NOT hardcode any [URL][] other than the path to the [Get Ledger Metadata][] method. A ledger MAY host different objects and API methods at different hostnames or base URLs, as long as all client applications can dereference the URLs in the usual way.


### JSON

All methods communicate both ways using [JavaScript Object Notation (JSON)](http://www.json.org/) unless otherwise specified. A ledger MUST use the `Content-Type: application/json` header in responses to indicate that the message body contains JSON. A ledger MAY honor the `Accept` header of the request and return the data in other formats if the client requests them. A ledger MAY interpret the message bodies of requests (PUT and POST methods) as JSON, even if the `Content-Type` header is missing or indicates a different format. The Common Ledger API uses HTTP status codes to indicate the status of API operations; if the ledger encounters an error processing a request, it MUST NOT return an HTTP status code in the 200-299 range even if communication was successful.

Field names in the JSON objects defined by this API never contain literal period (`.`) characters. By convention, this documentation uses the `.` character to indicate fields nested inside other Object-type fields. In some cases, field values contain literal period (`.`) characters. Additionally, this field contains some objects that can hold arbitrary data. Arbitrary-data objects can contain any legal JSON, including field names with literal period (`.`) characters. Arbitrary-data objects SHOULD NOT contain duplicate keys.


### Amounts
[amount]: #amounts

The Common Ledger API represents numeric currency amounts as strings rather than native JSON numbers. This is because many standard libraries automatically decode numbers to a [IEEE 754 double precision floating point](https://en.wikipedia.org/wiki/IEEE_floating_point) representation. Using IEEE 754 double floats can introduce a loss of precision and rounding errors that are unacceptable for financial services, depending on the range and use cases needed. (In particular, digital assets that are natively represented as 64-bit unsigned integers do not fit properly into IEEE 754 double precision floats.) Amounts in the Common Ledger API MUST match the following regular expression:

`^[-+]?[0-9]*[.]?[0-9]+([eE][-+]?[0-9]+)?$`

Client applications can decode numeric strings to whatever representation provides sufficient precision for their specific needs. The ledger should report information about the precision it uses in the [ledger metadata][Get Ledger Metadata] response.


### Assets and Currency

The Common Ledger API provides access to a ledger containing a single currency or asset. The [Get Ledger Metadata][] method reports the type of asset or currency used, as an [Asset resource][].

If a provider supports multiple currencies, the provider can server Common Ledger APIs separately for each currency. For each method described in this document, there would be a version of it prefixed by a different currency code. For example, the [Prepare Transfer][] method could be available for different currencies at the following locations:

- `POST https://ledger.example.com/TZS/transfers`
- `POST https://ledger.example.com/KES/transfers`

These instances could be served by the same underlying software and share infrastructure, but it would not be possible to transfer directly from one to the other, since the currency denominations are different. An **ILP Connector** could facilitate cross-currency payments.


### Scope

The Common Ledger API does not define the full range of functionality needed by a functional ledger. This API defines the parts the ILP Client needs, and leaves other parts to the discretion of the ledger implementer. For a fully-functional reference implementation, see the [five-bells-ledger](https://github.com/interledgerjs/five-bells-ledger).


### Authorization and Authentication

The ledger MUST authenticate API clients using any of the following methods:

- [HTTP Basic Auth](https://tools.ietf.org/html/rfc2617#section-2)
- [TLS Client Certificates](https://tools.ietf.org/html/rfc5246#section-7.4.6)
- Token-based authentication. A ledger MUST support token-based auth for [WebSocket][] connections; the ledger MAY support token-based auth for other methods. See also: [Get Auth Token][].

The ledger MUST support authenticating a client as the owner of a specific account, so that it can grant or restrict access to certain methods. A ledger MAY define additional authorization levels, especially for functions that extend this API. We suggest the following authorization levels:

- Administrator - Full control over all ledger operations.
- Account owner (for a specific account) - Can perform operations relating to one specific account, such as authorizing debits from or credits to the account, and viewing the account balance.
- Unauthorized. Read-only access to some global ledger data.


## Data Types

### Transfer Resource
[Transfer resource]: #transfer-resource

A transfer represents money being moved around _within a single ledger_. A transfer debits one account and credits another account for the exact same amount. The Common Ledger API does not define a way to add or remove money from the ledger; the methods defined here always maintain a zero sum across all account balances. However, you can effectively add money to a ledger by transferring it from an "issuer" account whose balance is allowed to go negative.

A transfer can be conditional upon a supplied [Crypto-Condition][], in which case it executes automatically when presented with the fulfillment for the condition. (Assuming the transfer has not expired or been canceled first.) If no crypto-condition is specified, the transfer is unconditional, and executes as soon as it is prepared.

A transfer object contains the fields from the following table. Some fields are _Server-provided_, meaning they cannot be set directly by clients. Fields that are "Optional" or "Server-provided" in the following table may be omitted by clients submitting transfer objects to the API, but **those fields are not optional to implement**. All fields, including the `memo` fields, must be implemented for the Common Ledger API to work properly. Fields of nested objects are indicated with a dot (`.`) character; no field names contain a dot literal.

| Name                   | Type                 | Description                  |
|:-----------------------|:---------------------|:-----------------------------|
| `client_id`            | [UUID][]             | Client-provided UUID for this resource. MUST be unique within the ledger. |
| `ledger`               | [URL][]              | Resource identifier for the ledger where the transfer occurs. MUST be an HTTP(S) URL where you can [get the ledger metadata][Get Ledger Metadata]. |
| `debit_account`        | [URL][]              | Resource identifier for the account debited in this transfer. MUST be an HTTP(S) URL where you can [get the account resource][Get Account]. |
| `credit_account`       | [URL][]              | Resource identifier for the account credited in this transfer. MUST be an HTTP(S) URL where you can [get the account resource][Get Account]. This can be the same as the `debit_account`. (Transfers where the `credit_account` is the `debit_account` are used for ILP transfers to sub-ledgers.) |
| `amount`               | String               | The [amount][] of the currency/asset being transferred. This is debited from the `debit_account` and credited to the `credit_account` when the transfer executes. |
| `execution_condition`  | [Crypto-Condition][] | _(Optional)_ The condition for executing the transfer. If omitted, the transfer executes unconditionally. |
| `expires_at`           | [Date-Time][]        | _(Optional)_ The date when the transfer expires and can no longer be executed. |
| `additional_info`      | Object               | _(Optional)_ Arbitrary fields attached to this transfer. (For example, the IDs of related transfers in other systems.) |
| `memo`                 | Object               | _(Optional)_ Arbitrary data provided by the `debit_account` for the `credit_account`. The connector stores the ILP Header in this field. |
| `note_to_self`         | Object               | _(Optional)_ Arbitrary data provided by the `debit_account` for itself. This field MUST be hidden when not authenticated as the `debit_account` or an admin. |
| `id`                   | [URL][]              | _(Server-provided)_ Primary resource identifier for this transfer. MUST be an HTTP(S) URL where you can [get the transfer resource][Get Transfer]. |
| `fulfillment`          | [URL][]              | (Server-provided) Path to the fulfillment for this transfer. MUST be an HTTP(S) URL where the client can [submit the fulfillment][Submit Fulfillment] or [get the fulfillment][Get Transfer Fulfillment]. MUST be provided if and only if this transfer has an `execution_condition`. |
| `transfer_rejection`   | [URL][]              | (Server-provided) Path where a client can [reject this transfer][Reject Transfer]. MUST be an HTTP(S) URL. |
| `rejection_reason`     | String               | _(Server-provided)_ The reason the transfer was rejected. MUST appear if and only if `state` is `rejected`. |
| `state`                | String               | _(Server-provided)_ The current state of the transfer. Valid states are `prepared`, `executed`, and `rejected`. |
| `timeline`             | Object               | _(Server-provided)_ Timeline of the transfer's state transitions. |
| `timeline.executed_at` | [Date-Time][]        | _(Server-provided)_ Time when the transfer was originally executed. MUST appear if and only if `state` is `executed`. This time MUST be equal to or later than the `prepared_at` time. |
| `timeline.prepared_at` | [Date-Time][]        | _(Server-provided)_ Time when the transfer was originally prepared. MUST appear, even if the transaction is unconditional. |
| `timeline.rejected_at` | [Date-Time][]        | _(Server-provided)_ Time when the transfer was originally rejected. MUST appear if and only if `state` is `rejected`. This time MUST be equal to or later than the `prepared_at` time. |

[UUID]: http://en.wikipedia.org/wiki/Universally_unique_identifier


#### Client IDs

The transfer's `client_id` field is one of the main ways of identifying the transfer; it is unique across the ledger, so implementations MAY use it as a primary unique key in a database. The client applications, not the server, generate the `client_id`, so the server SHOULD require that the field match the canonical form for a [UUID][], which is 32 lowercase hexadecimal digits, separated by hyphens into groups of 8-4-4-4-12.

Depending on what algorithm clients use to generate UUIDs, it may be possible for other account owners to guess in advance which UUIDs might be used, and could preemptively claim `client_id` values that other account owners might use. A ledger MAY discourage this "squatting" behavior by imposing a limit on how many new transfers an account can generate within a fixed period of time, or with other similar limits. (A ledger could also address this issue in other ways, such as charging a fee for preparing transfers.) Client applications SHOULD use a sufficiently hard-to-predict system for generating UUIDs, such as the random algorithm described in [RFC4122](https://www.ietf.org/rfc/rfc4122).


### Account Resource
[Account resource]: #account-resource

An account resource contains the fields in the following table. Some fields are _Server-provided_, meaning they cannot be set directly by clients. Fields that are "Optional" or "Server-provided" in the following table may be omitted by clients submitting objects to the API, but those fields are not optional to implement. Fields of nested objects are indicated with a dot (`.`) character; no fields contain a dot literal.

| Name                      | Type    | Description                            |
|:--------------------------|:--------|:---------------------------------------|
| `name`                    | String  | Name of the account. A ledger MAY require this to be unique. MUST match the regular expression `^[a-zA-Z0-9._~-]{1,256}$`. |
| `fingerprint`             | String  | _(Optional)_ A fingerprint of the account's client certificate. This field MUST be available if and only if the ledger supports client certificate authentication. MUST match the regular expression `^[0-9A-Fa-f]{2}(:[0-9A-Fa-f]{2}){19,127}$`. |
| `ledger`                  | [URL][] | _(Optional)_ The path to the ledger containing this account. MUST be an HTTP(S) URL where the client can [Get Ledger Metadata][]. |
| `minimum_allowed_balance` | String  | _(Optional)_ The minimum balance permitted on this account. The special value `"-infinity"` indicates no minimum balance. This is a string so that no precision is lost in JSON encoding/decoding. The default value SHOULD be `"0"`. |
| `id`                      | [URL][] | _(Server-provided)_ The primary, unique identifier for this account. MUST be an HTTP(S) [URL][] where the client can [get this resource][Get Account]. |
| `balance`                 | String  | _(Server-provided)_ Balance as decimal [amount][]. Defaults to `"0"`. This can be negative, if the account's `minimum_allowed_balance` allows it. |

A ledger MAY define additional fields for the account resource. For example, `is_admin` could be a boolean that, if true, grants administrator-level authorization when authenticated as the account owner.


### Message Resource
[Message resource]: #message-resource

Messages are sent through the ledger's [Send Message][] method and received in a [WebSocket][] subscription. All fields of the message are required:

| Field    | Value   | Description                                             |
|:---------|:--------|:--------------------------------------------------------|
| `ledger` | [URL][] | The base [URL][] of this ledger. MUST be an HTTP(S) URL where the client can [Get Ledger Metadata][]. |
| `from`   | [URL][] | Resource identifier of the account sending the message. MUST be an HTTP(S) URL where the client can [get account information][Get Account]. |
| `to`     | [URL][] | Resource identifier of the account receiving the message. MUST be an HTTP(S) URL where the client can [get account information][Get Account]. |
| `data`   | Object  | The message to send, containing arbitrary data. A ledger MAY set a maximum length on messages, but that limit MUST NOT be less than 510 UTF-8 characters or 2,048 bytes. |


### Asset Resource
[Asset resource]: #asset-resource

There are many kinds of resources that can be tracked in a ledger. The Asset Resource describes the resource tracked in this ledger, so that client applications can display appropriate information to users. An asset resource has the following fields:

| Field            | Value     | Description                                   |
|:-----------------|:----------|:----------------------------------------------|
| `type`           | String    | The type of asset. Currently, the only supported type is `iso4217-currency`. |
| `code`           | String    | The currency code to represent this asset. For `iso4217-currency` assets, this MUST be a three-letter uppercase [ISO 4217](http://www.xe.com/iso4217.php) currency code. |
| `symbol`         | String    | Symbol to use in user interfaces with amounts of this asset. For example, "$". |
| `decimal_digits` | Number    | _(Optional)_ Typical number of decimal places to display for amounts of this asset. MUST be a non-negative integer. This MAY be different from the precision and scale used internally by the ledger, which are reported in the [Get Ledger Metadata][] field. |
| ...              | (Various) | Depending on the `type` of the asset, additional fields may be provided. |

### Crypto-Conditions
[Crypto-Condition]: #crypto-conditions
[Crypto-Condition Fulfillment]: #crypto-conditions

The [Crypto-Conditions spec](https://github.com/interledger/rfcs/tree/master/0002-crypto-conditions) defines standard formats for _conditions_ and _fulfillments_.

Conditions are distributable event descriptions, and fulfillments are cryptographically verifiable messages that prove an event occurred. If you transmit a fulfillment, then everyone who has the corresponding condition can agree that the condition has been met.

Crypto-conditions control the execution of conditional transfers. The Common Ledger API supports conditions and fulfillments in text format.

The Crypto-Conditions specification anticipates that it will need to expand to keep up with changes in the field of cryptography, so conditions always define which rules and algorithms are necessary to verify the fulfillment. Implementations can use the condition's feature list to determine if they can properly process the fulfillment, without having seen the fulfillment itself.

Example condition in string format:

    cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66

Example fulfillment in string format:

    cf:0:VGhlIG9ubHkgYmFzaXMgZm9yIGdvb2QgU29jaWV0eSBpcyB1bmxpbWl0ZWQgY3JlZGl0LuKAlE9zY2FyIFdpbGRl

The [five-bells-condition](https://github.com/interledgerjs/five-bells-condition) library provides a JavaScript implementation of Crypto-Conditions. For custom implementations, consider the latest version of the [IETF crypto-conditions spec](https://tools.ietf.org/html/draft-thomas-crypto-conditions-00) as the source of truth.


### URLs
[URL]: #urls
[URLs]: #urls
[RFC6570]: https://tools.ietf.org/html/rfc6570

The Common Ledger API uses URLs as the main way of identifying and looking up resources in the API. These URLs should be formatted as valid _absolute URLs_ in accordance with the [WHATWG URL Living Standard](https://url.spec.whatwg.org/). The URLs SHOULD use the `https:` scheme, except for some [WebSocket][] paths that use the `wss:` scheme instead. In development or private subnetworks, `http:` and `ws:` are acceptable instead.

The `urls` field of the [Get Ledger Metadata][] method returns a list of paths to other API methods. Each member of the `urls` field describes one path, which MUST be an HTTP(S)-formatted URL unless otherwise specified. Some paths contain [RFC6570][]-formatted variable sections in curly braces. The `urls` field MUST include all of the following:

| Path name              | Variables     | HTTP Method | API Method(s)         |
|:-----------------------|:--------------|:------------|:----------------------|
| `transfers`            | None          | POST        | [Prepare Transfer][]   |
| `websocket`            | None          | N/A path    | [WebSocket][] (MUST be a `ws://` or `wss://` URL.) |
| `transfer`             | `{client_id}` | GET         | [Get Transfer][]      |
| `transfer_rejection`   | `{client_id}` | PUT         | [Reject Transfer][]   |
| `transfer_fulfillment` | `{client_id}` | GET, PUT    | [Get Transfer Fulfillment][], [Submit Fulfillment][] |
| `account`              | `{name}`      | GET         | [Get Account][]       |

The `urls` field of the metadata MAY also contain other methods provided by the ledger.

Some resources also contain fields whose values are URLs pointing to other methods. These URLs MUST NOT contain [RFC6570][]-formatted variable sections. The following table maps URL fields to the API methods that can be accessed at those paths:

| Resource | Field                | HTTP Method | API Method                   |
|:---------|:---------------------|:------------|:-----------------------------|
| Transfer | `id`                 | GET         | [Get Transfer][]             |
| Transfer | `ledger`             | GET         | [Get Ledger Metadata][]      |
| Transfer | `fulfillment`        | PUT         | [Submit Fulfillment][]       |
| Transfer | `fulfillment`        | GET         | [Get Transfer Fulfillment][] |
| Transfer | `transfer_rejection` | PUT         | [Reject Transfer][]          |
| Transfer | `debit_account`      | GET         | [Get Account][]              |
| Transfer | `credit_account`     | GET         | [Get Account][]              |
| Message  | `from`               | GET         | [Get Account][]              |
| Message  | `to`                 | GET         | [Get Account][]              |
| Message  | `ledger`             | GET         | [Get Ledger Metadata][]      |


### Date-Time
[Date-Time]: #date-time

All dates and times should be expressed in [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) date-time format with precision to the second or millisecond. The time zone offset should always be `Z`, for no offset. In other words, the date-time should be a **string** matching the one of the following formats:

| Precision   | Format                     |
|:------------|:---------------------------|
| Second      | `YYYY-MM-DDTHH:mm:ss.sssZ` |
| Millisecond | `YYYY-MM-DDTHH:mm:ssZ`     |


## API Methods

### Get Ledger Metadata
[Get Ledger Metadata]: #get-server-metadata

Receive information about the ledger.

**Authorization:** This method MUST be accessible to all clients authorized as account owners or administrators. This method MAY be accessible to unauthorized users.

#### Request Format

```
GET /
```

**Metadata URL Name:** None (top-level path for the ledger)

##### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON object with the following fields. (A field name like `foo[].bar` indicates that the row describes the field `bar` in _each_ object contained in the array `foo`.)

| Field               | Value              | Description                       |
|:--------------------|:-------------------|:----------------------------------|
| `asset_info`        | [Asset resource][] | Information on the currency or other asset this ledger tracks. |
| `ilp_prefix`        | String             | The ILP Address prefix of the ledger. This must match the regular expression `^[a-zA-Z0-9._~-]+\.$` |
| `connectors`        | Array of Objects   | Accounts belonging to recommended ILP Connectors. This list MAY be empty. |
| `connectors[].id`   | [URL][]            | The unique ID of this connector's account. This is used when [messaging](#send-message) the connectors to get quotes. MUST be an HTTP(S) URL where a client can [Get Account][]. |
| `connectors[].name` | [URL][]            | The unique `name` field of this connector's account. |
| `precision`         | Integer            | How many total decimal digits of precision this ledger uses to represent currency amounts. |
| `scale`             | Integer            | How many digits after the decimal place this ledger supports in currency amounts. |
| `urls`              | Object             | Paths to other methods exposed by this ledger. Each field name is short name for a method and the value is the path to that method. Some fields MUST be present; see [URLs][] for details. |
| `rounding`          | String             | _(Optional)_ The type of rounding used internally by ledger for values that exceed the reported `scale` or `precision`. If provided, the value MUST be `floor`, `ceiling`, or `nearest`. |
| ...                 | (Various)          | _(Optional)_ Additional arbitrary values as desired. |

#### Example

Request:

```
GET /
```

Response:

```json
HTTP/1.1 200 OK

{
  "currency_code": null,
  "currency_symbol": null,
  "connectors": [{
    "id": "https://red.ilpdemo.org/ledger/accounts/connie",
    "name": "connie"
  }],
  "urls": {
    "health": "http://usd-ledger.example/health",
    "transfers": "http://usd-ledger.example/transfers",
    "transfer_fulfillment": "http://usd-ledger.example/transfers/{client_id}/fulfillment",
    "account": "http://usd-ledger.example/accounts/{name}",
    "websocket": "wss://usd-ledger.example/websocket/"
  },
  "precision": 10,
  "scale": 2
}
```


#### Errors

- This method does not return any errors under normal circumstances.


### Prepare Transfer
[Prepare Transfer]: #prepare-transfer

Prepares a new transfer (conditional or unconditional) in the ledger. When a transfer becomes prepared, it executes immediately if there is no condition. If you specify `execution_condition`, the funds are held until the beneficiary [submits the matching fulfillment][Submit Fulfillment] or the `expires_at` time is reached.

**Authorization:** The owner of an account MUST be able to prepare a conditional transfer that debits the account. Non-administrators MUST NOT be able to prepare a transfer that debits a different account. A ledger MAY disallow non-administrators from preparing unconditional transfers.

#### Request Format

POST a JSON [Transfer resource][] to the `transfers` [URL][].

**Metadata URL Name:** `transfers`

##### Body Parameters

The message body should be a JSON [Transfer resource][].

#### Response Format

A successful result uses the HTTP response code **201 Created** and contains a JSON body with the [Transfer resource][] as saved.

#### Example

Request:

```json
POST /transfers
Content-Type: application/json

{
  "client_id": "3a2a1d9e-8640-4d2d-b06c-84f2cd613204",
  "ledger": "http://usd-ledger.example",
  "debit_account": "http://usd-ledger.example/accounts/alice",
  "credit_account": "http://usd-ledger.example/accounts/bob",
  "amount": "50",
  "execution_condition": "cc:0:3:8ZdpKBDUV-KX_OnFZTsCWB_5mlCFI3DynX5f5H2dN-Y:2",
  "expires_at": "2016-10-25T08:41:59.795Z"
}
```

Response:

```json
HTTP/1.1 201 Created

{
  "id": "http://usd-ledger.example/transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204",
  "client_id": "3a2a1d9e-8640-4d2d-b06c-84f2cd613204",
  "ledger": "http://usd-ledger.example",
  "debit_account": "http://usd-ledger.example/accounts/alice",
  "credit_account": "http://usd-ledger.example/accounts/bob",
  "amount": "50",
  "execution_condition": "cc:0:3:8ZdpKBDUV-KX_OnFZTsCWB_5mlCFI3DynX5f5H2dN-Y:2",
  "expires_at": "2016-10-25T08:41:59.795Z",
  "state": "prepared",
  "timeline": {
    "prepared_at": "2015-06-16T00:00:01.000Z"
  }
}
```

#### Errors

- [InsufficientFundsError][] - The `debit_account` would go below its `minimum_allowed_balance` if this transfer were executed
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem.
- [AlreadyExistsError][] - The `client_id` supplied is already used by another transfer.
- [InvalidUriParameterError][] - One of the [URL][] or [UUID][] parameters was not formatted properly.
- [InvalidBodyError][] - The request body was not properly-formatted JSON, or did not match the Content-Type provided.
- [UnsupportedCryptoConditionError][] - The transfer included an `execution_condition` whose feature bitstring requires functionality not implemented by this ledger.


### Submit Fulfillment
[Submit Fulfillment]: #submit-fulfillment

Execute a transfer by submitting a [Crypto-Condition Fulfillment][]. To execute a transfer, the transfer MUST begin in the `prepared` state and the submitted fulfillment must satisfy the [Crypto-Condition][] in the transfer's `execution_condition` field. Doing so transitions the transaction to `executed`.

**Authorization:** The owner of an account MUST be able to submit the fulfillment for a transfer that credits the account. A ledger MAY allow other account owners or unauthorized clients to submit a fulfillment. (If only the `credit_account` can submit a fulfillment, then crediting an account with a conditional transfer effectively requires permission from the account owner.)

#### Request Format

PUT to the `fulfillment` path of the transfer you want to execute, with the header `Content-Type: application/json` and a message body containing the fulfillment.

**Metadata URL Name:** `transfer_fulfillment`. Suggested generic path: `/transfers/{client_id}/fulfillment`

**Caution:** The ledger _MUST_ require the `Content-Type: application/json` header on this request. In the future, the API might also accept fulfillments in binary fulfillment at this same endpoint.

##### Body Parameters

The message body should be a JSON object with one field, `fulfillment`, which contains a [Crypto-Condition Fulfillment][] in string format.

#### Response Format

A successful result uses the HTTP response code **201 Created**. The message body of the response is a JSON object containing the submitted fulfillment in the `fulfillment` field. A ledger MUST return a successful response if and only if the transfer was executed as a result of this request.

If you

#### Example

Request:

```json
PUT /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/fulfillment
Content-Type: application/json

{
  "fulfillment": "cf:0:_v8"
}
```

Response:

```json
HTTP/1.1 200 OK

{
  "fulfillment": "cf:0:_v8"
}
```

#### Errors

- [NotFoundError][] - The transfer does not exist.
- [UnmetConditionError][] - The fulfillment does not match the condition.
- [TransferNotConditionalError][] - The transfer had no condition to fulfill.
- [TransferStateError][] - The transfer was not in the `prepared` state when the request was received. This occurs if the transfer has already been executed, rejected, or expired.
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem.
- [InvalidBodyError][] - The request body was not properly-formatted JSON.


### Reject Transfer
[Reject Transfer]: #reject-transfer

Reject a prepared transfer. A transfer can be rejected if and only if that transfer is in the `prepared` state. Doing so transitions the transfer to the `rejected` state.

**Authorization:** The `credit_account` of a transfer MUST be able to reject the transfer. Unauthorized users and the `debit_account` MUST NOT be able to reject the transfer. Other account owners MUST NOT be able to reject the transfer unless those accounts are explicitly authorized to do so by the `credit_account` and those accounts are not the `debit_account`.

#### Request Format

PUT to the `transfer_rejection` path of the transfer you want to execute, with a JSON object in the message body containing a rejection reason.

**Metadata URL Name:** `transfer_rejection`. Suggested generic path: `/transfers/{client_id}/rejection`

##### Body Parameters

The message body should be a JSON object with one top-level field:

| Field              | Value  | Description                                    |
|:-------------------|:-------|:-----------------------------------------------|
| `rejection_reason` | String | The reason for rejecting the transfer. This is intended to be a machine-readable identifier. |

#### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON object containing the updated [Transfer resource][] containing the rejection reason.

#### Example

Request:

```json
PUT /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/rejection
Content-Type: application/json

{
  "rejection_reason": "BlacklistedSender"
}
```

Response:

```json
HTTP/1.1 200 OK

{
  "ledger": "https://red.ilpdemo.org/ledger",
  "client_id": "63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "debit_account": "https://red.ilpdemo.org/ledger/accounts/alice",
  "credit_account": "https://red.ilpdemo.org/ledger/accounts/bob",
  "amount": "199.99",
  "execution_condition": "cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66",
  "expires_at": "2018-01-01T00:00:00.000Z",
  "memo": {
    "ilp_header": {
      "version": 1,
      "destinationAddress": "ilpdemo.blue.bob",
      "destinationAmount": "199.0"
    }
  },
  "note_to_self": {
    "foo": "bar"
  },
  "id": "https://red.ilpdemo.org/ledger/transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "fulfillment": "https://red.ilpdemo.org/ledger/transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf/fulfillment",
  "state": "rejected",
  "timeline": {
    "prepared_at": "2016-10-21T22:45:01.000Z",
    "cancelled_at": "2016-10-22T21:33:34.867Z"
  },
  "rejection_reason": "BlacklistedSender"
}
```

#### Errors

- [NotFoundError][] - The transfer does not exist.
- [UnprocessableEntityError][] - The request is formatted properly but contains an otherwise-unspecified semantic problem. This includes cases where the transfer has already been executed or rejected.
- [InvalidBodyError][] - The request body was not properly-formatted JSON.
- [TransferStateError][] - The transfer was not in the `prepared` state when the request was received. This occurs if the transfer has already been rejected or executed.


### Get Transfer
[Get Transfer]: #get-transfer

Check the details or status of a local transfer.

**Authorization:** The owners of the `debit_account` and `credit_account` MUST be able to get the transfer. A ledger MAY allow other account owners or unauthorized clients to get a transfer.

#### Request Format

GET the path in the `id` field of a transfer object.

**Metadata URL Name:** `transfer`. Suggested generic path: `/transfers/{client_id}`

#### Response Format

A successful result uses the HTTP response code **200 OK** and contains a JSON body with the requested [Transfer resource][].

#### Example

Request:

```
GET /ledger/transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf
```

Response:

```json
HTTP/1.1 200 OK

{
  "ledger": "https://red.ilpdemo.org/ledger",
  "client_id": "63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "debit_account": "https://red.ilpdemo.org/ledger/accounts/alice",
  "credit_account": "https://red.ilpdemo.org/ledger/accounts/bob",
  "amount": "199.99",
  "execution_condition": "cc:0:3:dB-8fb14MdO75Brp_Pvh4d7ganckilrRl13RS_UmrXA:66",
  "expires_at": "2018-01-01T00:00:00.000Z",
  "memo": {
    "ilp_header": {
      "version": 1,
      "destinationAddress": "ilpdemo.blue.bob",
      "destinationAmount": "199.0"
    }
  },
  "note_to_self": {
    "foo": "bar"
  },
  "id": "https://red.ilpdemo.org/ledger/transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf",
  "fulfillment": "https://red.ilpdemo.org/ledger/transfers/63a61fa9-fca2-4779-9d50-49dc691b8fbf/fulfillment",
  "state": "rejected",
  "timeline": {
    "prepared_at": "2016-10-21T22:45:01.000Z",
    "cancelled_at": "2016-10-22T21:33:34.867Z"
  },
  "rejection_reason": "BlacklistedSender"
}
```

#### Errors

- [NotFoundError][]
- [InvalidUriParameterError][]


### Get Transfer Fulfillment
[Get Transfer Fulfillment]: #get-transfer-fulfillment

Retrieve the fulfillment for a transfer that has been executed or canceled. This is separate from the [Transfer resource][] because it can be very large.

**Authorization:** The ledger MUST allow owners of the `credit_account` and `debit_account` to get the transfer's fulfillment. A ledger MAY allow other account owners or unauthorized users to get a transfer's fulfillment.

#### Request Format

GET the path specified in the `fulfillment` field of the transfer.

**Metadata URL Name:** `transfer_fulfillment`. Suggested generic path: `/transfers/{client_id}/fulfillment`

##### URL Parameters

| Field       | Value | Description                                            |
|:------------|:------|:-------------------------------------------------------|
| `client_id` | UUID  | The [UUID][] of the Transfer whose fulfillment to retrieve. |

#### Response Format

A successful result uses the HTTP response code **200 OK**. The body contains a JSON object with the following field:

| Field | Value | Description |
|---|---|---|
| `fulfillment` | String | The Transfer's [Crypto-Condition Fulfillment][] in text format. |

#### Example

Request:

```
GET /transfers/3a2a1d9e-8640-4d2d-b06c-84f2cd613204/fulfillment
```

Response:

```json
HTTP/1.1 200 OK

{
  "fulfillment": "cf:0:_v8"
}
```

#### Errors

- [NotFoundError][]
- [InvalidUriParameterError][]


### Get Account
[Get Account]: #get-account

Get an account resource.

**Authorization:** The owner of an account MUST be able to get the account resource. A ledger MAY allow other account owners or unauthorized users to get other account resources. A ledger MAY return a subset of fields when it returns an account resource to any client other than the account owner (for example, omitting the balance).

#### Request Format

GET the path from the `debit_account` or `credit_account` field of a transfer.

**Metadata URL Name:** `account`. Suggested generic path: `/accounts/{name}`

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


### Send Message
[Send Message]: #send-message

Try to send a notification to another account. The message is only delivered if the other account is subscribed to [account notifications](#subscribe-to-account) on a WebSocket connection. ILP Connectors use this method to share quote information.

#### Request Format

POST a JSON [Message resource][] to the `message` [URL][].

**Metadata URL Name:** `message`. Suggested generic path: `message`

#### Response Format

A successful response uses the HTTP response code **204 No Content** and contains no message body.

#### Example

Request:

```json
POST /messages
Content-Type: application/json

{
  "from": "https://blue.ilpdemo.ripple.com/ledger/accounts/bob",
  "to": "https://blue.ilpdemo.ripple.com/ledger/accounts/alice",
  "ledger": "https://blue.ilpdemo.ripple.com/ledger",
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

**Note:** This example uses the [Interledger Quoting Protocol](https://github.com/interledger/rfcs/blob/master/0008-interledger-quoting-protocol/0008-interledger-quoting-protocol.md) quote request type as example data. However, the `data` field may contain arbitrary objects, so the ledger MUST NOT require a specific format for such data.


Response:

```
HTTP/1.1 204 No Content
```

#### Errors

- [InvalidBodyError][]
- [InvalidUriParameterError][]
- [UnprocessableEntityError][]


### Get Auth Token
[Get Auth Token]: #get-auth-token

Get a token that can be used to authenticate future requests.

**Note:** This method is REQUIRED for ledgers to authenticate [WebSocket][] connections. If the ledger does not authenticate WebSocket connections, this method is OPTIONAL. The ledger MAY allow clients to authenticate for any other methods of the API using the tokens returned by this method.

#### Request Format

GET the `auth_token` [URL][].

Depending on the [authentication mechanism](#authorization-and-authentication) used by this ledger, the ledger MAY require the HTTP `Auth` header with a valid username and password, or the ledger may require a different method of authentication.

**Metadata URL Name:** `auth_token`.

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




## WebSocket
[WebSocket]: #websocket

**Metadata URL Name:** `websocket`. Suggested generic path: `/websocket` (with `wss://` protocol)

Clients can subscribe to live, read-only notifications of ledger activity by opening a [WebSocket](https://developer.mozilla.org/en-US/docs/Web/API/WebSockets_API) connection to this path and sending a subscription request.

### WebSocket Authentication

A ledger MAY require clients to authenticate themselves using a token in the `token` query parameter. If the ledger supports authentication, it MAY restrict the data that can be accessed, as long as it complies with the following rules:

- An account owner MUST be able to subscribe to changes to its own account.
- An account owner MUST be able to subscribe to changes to transactions where the account is the `credit_account` _or_ `debit_account`.
- An account owner MUST be able to subscribe to messages to its account. Account owners and unauthorized users MUST NOT be able to subscribe to messages to other accounts.

The authentication you use when opening the connection applies to all subscriptions made in the connection.

A ledger MUST support multiple independent WebSocket connections with the same authentication. (This provides connection redundancy for notifications, which is important for ILP connectors.)

### WebSocket Messages

After the connection is established, the client and ledger communicate by passing [JSON-RPC 2.0](http://www.jsonrpc.org/specification) messages back and forth. Both the client and ledger can take the roles of "client" and "server" in JSON-RPC terms. The client can submit requests to subscribe or unsubscribe from specific categories of message. The ledger responds directly to the client's requests with confirmation messages, and also sends "notification" requests to the client. (Notifications are identified by the `id` value `null`.)

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
| `params.eventType` | String           | _(Optional)_ Types of events to subscribe to. May contain a wildcard character. See [Event Types][] for a full list of types. If omitted, subscribes to all event types. |
| `params.accounts`  | Array            | Each member of this array must be the [URL][] of an account to subscribe to, as a string. This replaces existing subscriptions; if the array length is zero, the client is unsubscribed from all account notifications. |

##### EventType Values
A client can include a wildcard in the `params.eventType` field to subscribe to a subset of event values. The ledger MUST support at least one trailing `*` as a wildcard character. For example, the following cases should all be valid:

- `transfer.update` - subscribes to events with the exact `event` value `transfer.update` only.
- `transfer.*` - subscribes to all events with the event value starting in `transfer.`, including at least `transfer.create` and `transfer.update`.
- `*` - subscribes to all events. (Equivalent to omitting the `eventType` filter when subscribing.)

##### Response
The ledger acknowledges the request immediately by sending a JSON object with the following fields:

| Field     | Value            | Description                                   |
|:----------|:-----------------|:----------------------------------------------|
| `id`      | String or Number | The `id` value from the request. This helps distinguish responses from other messages. |
| `jsonrpc` | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 message. |
| `result`  | Number           | Updated number of active account subscriptions on this WebSocket connection. In practice, this is usually the length of the `params` array from the request. |

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
      "params": ["https://ledger.example/accounts/alice"],
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

| Field     | Value            | Description                                   |
|:----------|:-----------------|:----------------------------------------------|
| `id`      | String or Number | An arbitrary identifier for this request. MUST NOT be `null`. |
| `jsonrpc` | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 request. |
| `method`  | String           | MUST be the value `"subscribe_transfer"`.      |
| `params`  | Array            | Each member of this array must be the [URL][] of a transfer to subscribe to, as a string. This array replaces any existing transfer subscriptions on this WebSocket connection. If the array length is zero, the client is unsubscribed from all transfer notifications. |

##### Response
The ledger acknowledges the request immediately by sending a JSON object with the following fields:

| Field     | Value            | Description                                   |
|:----------|:-----------------|:----------------------------------------------|
| `id`      | String or Number | The `id` value from the request. This helps distinguish responses from other messages. |
| `jsonrpc` | String           | MUST have the value `"2.0"` to indicate this is a JSON-RPC 2.0 request. |
| `result`  | Number           | Updated number of active transfer subscriptions on this WebSocket connection. In practice, this is usually the length of the `params` array from the request. |

Later, the ledger responds with [notifications](#websocket-notifications) whenever any of the following occurs:

- The transfer changes state. For example, from prepared to executed or to expired. (`event` type: `transfer.update`)


#### WebSocket Notifications

The ledger sends notifications to connected clients when certain events occur, according to the current subscriptions of the clients. Every notification is sent at most once per WebSocket connection to the ledger, even if a client is subscribed to multiple categories of message that should prompt the same notification. (For example, if you are subscribed to the `credit_account` or `debit_account` of a transfer and subscribed to the transfer itself, you still receive only one notification.)

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
| `transfer.create` | [Transfer resource][] | Occurs when a new transfer is prepared. Sent to clients subscribed to the `debit_account` and/or the `credit_account`. If the transfer is unconditional, this notification indicates the state of the transaction after execution. The `related_resources` field is omitted. |
| `transfer.update` | [Transfer resource][] | Occurs when a transfer changes state from `prepared` to `executed` or `rejected`. If the transfer was executed, the `execution_condition_fulfillment` field of `related_resources` MUST contain the fulfillment. If the transfer was rejected, the `related_resources` field is empty. |
| `message.sent`    | [Message resource][]  | Occurs when someone else sends a message. |

If a ledger creates custom event types, their values should follow the convention `{resource}.{event}`.


## API Error Codes

The Common Ledger API may return errors using HTTP codes in the range 400-599, depending on the type of error. The message body of the error response is a JSON object with additional information about the nature of the error.

Every error response contains at least the following fields:

| Field      | Type   | Description                                            |
|:-----------|:-------|:-------------------------------------------------------|
| `error_id` | String | A unique error code for this specific type of error, such as `UnmetConditionError`. |
| `message`  | String | A longer, human-readable description for the cause of the error. |

Errors may also have additional arbitrary fields describing the cause or context of the error.

**Note:** Any fields other than `error_id` and `message` should be considered optional and informational. Clients MUST NOT depend on the presence of those fields. The examples in this spec contain suggestions for additional fields, but those should not be taken as requirements.

### Unauthorized
[Unauthorized]: #unauthorized

The [authentication information](#authorization-and-authentication) supplied to this request was insufficient for one of the following reasons:

- This method requires authentication but none was provided
- The credentials were provided using a system not supported by this method (e.g. Basic Auth when Client Certificates are required)
- The credentials were malformed or don't match the known account information

A ledger MAY return any message body using any content type with this error. (This makes it easier to use proxy servers and stock server configuration to handle authorization.)

**HTTP Status Code:** 401 Unauthorized

```json
HTTP/1.1 401 Unauthorized

{
  "error_id": "Unauthorized",
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
