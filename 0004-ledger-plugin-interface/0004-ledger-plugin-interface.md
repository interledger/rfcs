# Ledger Plugin Interface (Javascript)

The Interledger Protocol is a protocol suite for connecting blockchains and other ledgers.

This spec defines a Javascript ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols. While the exact methods and events defined here are specific to the Javascript implementation, this may be used as a guide for ledger abstractions in other languages.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP spec](../0003-interledger-protocol/).

## Class: LedgerPlugin
`class LedgerPlugin`

###### Methods
| | Name |
|:--|:--|
| `new` | [**LedgerPlugin**](#new-ledgerplugin) ( opts ) |
| | [**connect**](#connect) ( options ) `⇒ Promise.<null>` |
| | [**disconnect**](#disconnect) ( ) `⇒ Promise.<null>` |
| | [**isConnected**](#isconnected) ( ) `⇒ Boolean` |
| | [**getInfo**](#getinfo) ( ) <code>⇒ [LedgerInfo](#class-ledgerinfo)</code> |
| | [**getAccount**](#getaccount) ( ) `⇒ String` |
| | [**getBalance**](#getbalance) ( ) <code>⇒ Promise.&lt;String></code> |
| | [**getFulfillment**](#getfulfillment) ( transferId ) <code>⇒ Promise.&lt;String></code> |
| | [**sendTransfer**](#sendtransfer) ( transfer ) <code>⇒ Promise.&lt;null></code> |
| | [**sendMessage**](#sendmessage) ( message ) <code>⇒ Promise.&lt;null></code> |
| | [**fulfillCondition**](#fulfillcondition) ( transferId, fulfillment ) <code>⇒ Promise.&lt;null></code> |
| | [**rejectIncomingTransfer**](#rejectincomingtransfer) ( transferId, reason ) <code>⇒ Promise.&lt;null></code> |

###### Events
| Name | Handler |
|:--|:--|
| [**connect**](#event-connect) | `( ) ⇒` |
| [**disconnect**](#event-disconnect) | `( ) ⇒` |
| [**error**](#event-error) | `( ) ⇒` |
| [**incoming_transfer**](#event-_transfer) | <code>( transfer:[IncomingTransfer](#incomingtransfer) ) ⇒</code> |
| [**incoming_prepare**](#event-_prepare) | <code>( transfer:[IncomingTransfer](#incomingtransfer) ) ⇒</code> |
| [**incoming_fulfill**](#event-_fulfill) | <code>( transfer:[IncomingTransfer](#incomingtransfer), fulfillment:String ) ⇒</code> |
| [**incoming_reject**](#event-_reject) | <code>( transfer:[IncomingTransfer](#incomingtransfer), rejectionReason:[RejectionMessage](#class-rejectionmessage) ) ⇒</code> |
| [**incoming_cancel**](#event-_cancel) | <code>( transfer:[IncomingTransfer](#incomingtransfer), cancellationReason:[RejectionMessage](#class-rejectionmessage) ) ⇒</code> |
| [**incoming_message**](#event-_message) | <code>( message:[IncomingMessage](#incomingmessage) ) ⇒</code> |
| [**outgoing_transfer**](#event-_transfer) | <code>( transfer:[outgoingTransfer](#outgoingtransfer) ) ⇒</code> |
| [**outgoing_prepare**](#event-_prepare) | <code>( transfer:[outgoingTransfer](#outgoingtransfer) ) ⇒</code> |
| [**outgoing_fulfill**](#event-_fulfill) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), fulfillment:String ) ⇒</code> |
| [**outgoing_reject**](#event-_reject) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), rejectionReason:[RejectionMessage](#class-rejectionmessage) ) ⇒</code> |
| [**outgoing_cancel**](#event-_cancel) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), cancellationReason:[RejectionMessage](#class-rejectionmessage) ) ⇒</code> |
| [**info_change**](#event-info_change) | <code>( info:[LedgerInfo](#class-ledgerinfo) ) ⇒</code> |

###### Errors
| Name | Description |
|:--|:--|
| [**InvalidFieldsError**]() | Arguments or configuration were invalidated client-side |
| [**UnreachableError**]() | An error occured due to connection failure |
| [**TransferNotFoundError**]() | A requested transfer does not exist and cannot be fetched |
| [**MissingFulfillmentError**]() | A transfer has not yet been fulfilled, so the fulfillment cannot be fetched |
| [**DuplicateIdError**]() | A transfer with the same ID and different fields has been sent |
| [**AlreadyRolledBackError**]() | A requested transfer has already been timed out or rejected and cannot be modified |
| [**AlreadyFulfilledError**]() | A requested transfer has already been fulfilled and cannot be modified |
| [**TransferNotConditionalError**]() | A requested transfer is not conditional and cannot be rejected/fulfilled/etc. |
| [**NotAcceptedError**]() | An operation has been rejected due to ledger-side logic |
| [**NoSubscriptionsError**]() | A transfer or message cannot be delivered because there are no active websockets |

### Instance Management

#### new LedgerPlugin
<code>new LedgerPlugin( **opts** : [PluginOptions](#class-pluginoptions) )</code>

Create a new instance of the plugin. Each instance typically corresponds to a different ledger. However, some plugins MAY deviate from a strict one-to-one relationship and MAY use one instance for multiple (similar) ledgers or multiple instances to talk to the same ledger.

Throws `InvalidFieldsError` if the constructor is given incorrect arguments.

###### Parameters
| Name | Type | Description |
|:--|:--|:--|
| opts | <code>[PluginOptions](#class-pluginoptions)</code> | Object containing ledger-related settings. May contain plugin-specific fields. |

###### Example
```js
const ledgerPlugin = new LedgerPlugin({

  // auth parameters are defined by the plugin

  _store: {
    // persistence may be required for internal use by some ledger plugins
    // (e.g. when the ledger has reduced memo capability and we can only put an ID in the memo)
    // Store a value under a key
    put: (key, value) => {
      // Returns Promise.<null>
    },
    // Fetch a value by key
    get: (key) => {
      // Returns Promise.<Object>
    },
    // Delete a value by key
    del: (key) => {
      // Returns Promise.<null>
    }
  }
})
```

For a detailed description of these properties, please see [`PluginOptions`](#class-pluginoptions).

### Connection Management

#### connect
<code>ledgerPlugin.connect( options:[ConnectOptions](#class-connectoptions ) ⇒ Promise.&lt;null></code>

`options` is optional.

Initiate ledger event subscriptions. Once `connect` is called the ledger plugin MUST attempt to subscribe to and report ledger events. Once the connection is established, the ledger plugin should emit the [`connect`](#event-connect-) event. If the connection is lost, the ledger plugin SHOULD emit the [`disconnect`](#event-disconnect-) event. The plugin should ensure that the information returned by `getInfo` and `getAccount` is available and cached before emitting the [`connect`](#event-connect-) event.

Rejects with `InvalidFieldsError` if credentials are missing, and `NotAcceptedError` if credentials are rejected.
Rejects with `TypeError` if `options.timeout` is passed but is not a `Number`.

#### disconnect
<code>ledgerPlugin.disconnect() ⇒ Promise.&lt;null></code>

Unsubscribe from ledger events.

#### isConnected
<code>ledgerPlugin.isConnected() ⇒ Boolean</code>

Query whether the plugin is currently connected.

#### getInfo
<code>ledgerPlugin.getInfo() ⇒ [LedgerInfo](#class-ledgerinfo)</code>

Retrieve some metadata about the ledger. Plugin must be connected, otherwise the function should throw.

###### Example Return Value
```json
{
  "prefix": "us.fed.some-bank.",
  "currencyCode": "USD",
  "currencyScale": 4,
  "connectors": [ "us.fed.some-bank.chloe" ]
}
```

For a detailed description of these properties, please see [`LedgerInfo`](#class-ledgerinfo).

#### getAccount
<code>ledgerPlugin.getAccount() ⇒ String</code>

Get the ledger plugin's ILP address. This is given to senders to receive transfers to this account. Plugin must be connected, otherwise the function should throw.

The mapping from the ILP address to the local ledger address is dependent on the ledger / ledger plugin. An ILP address could be the `<ledger prefix>.<account name or number>`, or a token could be used in place of the actual account name or number.

###### Example Return Value
`us.fed.some-bank.my-account`

#### getBalance
<code>ledgerPlugin.getBalance() ⇒ Promise.&lt;String></code>

Return a (base-ten) integer string (`..., '-3', '-2', '-1', '0', '1', '2', '3', ...`) representing the current balance, in the ledger's base unit. For example, on a ledger with `currencyCode` 'USD' and `currencyScale` 6,
the base unit would be micro-dollars.
A balance of '1230000' should then be interpreted as equivalent to 1.23 US dollars. The maximum and minimum balance are up to the ledger to determine. Plugin must be connected, otherwise the promise should reject.

#### getFulfillment
<code>ledgerPlugin.getFulfillment( transferId ) ⇒ Promise.&lt;String></code>

Return the fulfillment of a transfer if it has already been executed.

Rejects with `MissingFulfillmentError` if the transfer exists but is not yet
fulfilled. Rejects with `TransferNotFoundError` if no conditional transfer is found
with the given ID. Rejects with `AlreadyRolledBackError` if the transfer has been rolled back
and will not be fulfilled. Rejects with `TransferNotConditionalError` if transfer is not
conditional.

#### Event: `connect`
<code>ledgerPlugin.on('connect', () ⇒ )</code>

Emitted whenever a connection is successfully established.

#### Event: `disconnect`
<code>ledgerPlugin.on('disconnect', () ⇒ )</code>

Emitted when the connection has been terminated or lost.

#### Event: `error`
<code>ledgerPlugin.on('error', ( **err**:Error ) ⇒ )</code>

General event for fatal exceptions. Emitted when the plugin experienced an unexpected unrecoverable condition. Once triggered, this instance of the plugin MUST NOT be used anymore.

### Ledger Transfers

Note that all transfers will have `transferId`'s to allow the plugin user to correlate actions related to a single transfer. The `transferId` will be the same as the ID used by the underlying ledger wherever possible or applicable. If the ledger does not have transfer IDs, the plugin may generate one and use the `store` passed in to the constructor to persist them.

#### sendTransfer
<code>ledgerPlugin.sendTransfer( **transfer**:[OutgoingTransfer](#outgoingtransfer) ) ⇒ Promise.&lt;null></code>

Plugin must be connected, otherwise the promise should reject. Initiates a ledger-local transfer. A transfer can
contain money and/or information. If there is a problem with the structure or
validity of the transfer, then `sendTransfer` should reject with an error.
If the transfer is accepted by the ledger, however, then
further errors will be in the form of `"reject"` events.

All plugins MUST implement zero-amount transfers, but some ledger plugins MAY
implement zero-amount transfers differently than other transfers.

###### Parameters
| Name | Type | Description |
|:--|:--|:--|
| transfer | <code>[OutgoingTransfer](#outgoingtransfer)</code> | Properties of the transfer to be created |

When sending transfers, the [id](#id), [amount](#amount) and [to](#to) fields
are required.

###### Returns
**`Promise.<null>`** A promise which resolves when the transfer has been submitted (but not necessarily accepted.)

Rejects with `InvalidFieldsError` if required fields are missing from the transfer or malformed. Rejects with `DuplicateIdError` if a transfer with
the given ID and different already exists. Rejects with `NotAcceptedError` if the transfer is rejected by the ledger due to insufficient balance or
a nonexistant destination account.

###### Example
```js
p.sendTransfer({
  id: 'd86b0299-e2fa-4713-833a-96a6a75271b8',
  to: 'example.ledger.connector',
  amount: '10',
  noteToSelf: {},
  executionCondition: '47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU',
  expiresAt: '2016-05-18T12:00:00.000Z'
})
```

For a detailed description of these properties, please see [`OutgoingTransfer`](#outgoingtransfer).

#### sendMessage
<code>ledgerPlugin.sendMessage( **message**:[OutgoingMessage](#outgoingmessage) ) ⇒ Promise.&lt;null></code>

Plugin must be connected, otherwise the promise should reject. Send a ledger-local message.
If there is a problem with the structure or validity of the message, then `sendMessage` should reject with an error.

Messaging is used by connectors for [quoting](../0008-interledger-quoting-protocol/) and broadcasting routes.

###### Parameters
| Name | Type | Description |
|:--|:--|:--|
| message | <code>[OutgoingMessage](#outgoingmessage)</code> | Properties of the message to be created |

When sending messages, the [to](#to) and [data](#data) fields are required.

###### Returns
**`Promise.<null>`** A promise which resolves when the message has been submitted (but not necessarily delivered). To ensure delivery, you must build a mechanism for that on top.

Rejects with `InvalidFieldsError` if required fields are missing from the message or malformed.
Rejects with `NotAcceptedError` if the message is rejected by the ledger.
Rejects with `NoSubscriptionsError` if the message cannot be delivered because there is nobody listening to messages addressed to the given account.


###### Example
```js
p.sendMessage({
  to: 'example.ledger.connector',
  data: { foo: 'bar' }
})
```

For a detailed description of these properties, please see [`OutgoingMessage`](#outgoingmessage).


#### fulfillCondition
<code>ledgerPlugin.fulfillCondition( **transferId**:String, **fulfillment**:String ) ⇒ Promise.&lt;null></code>

Submit a fulfillment to a ledger. Plugin must be connected, otherwise the promise should reject.

The `fulfillment` is an arbitrary 32-byte buffer and is provided as a base64url-encoded string.

Rejects with `InvalidFieldsError` if the fulfillment is malformed. Rejects with `TransferNotFoundError` if the fulfillment
if no conditional transfer with the given ID exists. Rejects with `AlreadyRolledBackError` if the transfer has already been
rolled back. Rejects with `NotAcceptedError` if the fulfillment is formatted correctly, but does not match the condition
of the specified transfer. Rejects with `TransferNotConditionalError` if transfer is not conditional.

#### rejectIncomingTransfer
<code>ledgerPlugin.rejectIncomingTransfer( **transferId**:String, **reason**:[RejectionMessage](#class-rejectionmessage) ) ⇒ Promise.&lt;null></code>

Reject an incoming transfer that is held pending the fulfillment of its `executionCondition` before the `expiresAt` time. `reason` MAY be supplied to provide details on why the transfer was rejected.

Rejects with `TransferNotFoundError` if there is no conditional transfer with the
given ID. Rejects with `AlreadyFulfilledError` if the specified transfer has already been
fulfilled. Rejects with `NotAcceptedError` if you are not authorized
to reject the transfer (e.g. if you are the sender). Rejects with `TransferNotConditionalError`
if transfer is not conditional.

This MAY be used by receivers or connectors to reject incoming funds if they will not fulfill the condition or are unable to forward the payment. Previous hops in an Interledger transfer would have their money returned before the expiry and the sender or previous connectors MAY retry and reroute the transfer through an alternate path.

### Event: `*_transfer`
<code style="">ledgerPlugin.on('incoming_transfer',
  (
    **transfer**:[Transfer](#class-transfer),
  ) ⇒
)</code>

Emitted after an outgoing/incoming transfer which does not have a condition is
executed on the ledger.

This indicates that the funds have already been
transferred. In order to prevent unexpected incoming funds, a ledger MAY allow users to forbid incoming transfers without
conditions.

If the event is `outgoing_transfer`, then it means you sent the transfer. `incoming_transfer` means somebody sent funds
to you.

### Event: `*_prepare`
<code style="">ledgerPlugin.on('incoming_prepare',
  (
    **transfer**:[Transfer](#class-transfer),
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer containing a condition is prepared.

Note that the `*_prepare` event **DOES NOT** indicate that money has been transferred. The final status will only be known when either the [*_fulfill](#event-_fulfill) or [*_cancel](#event-_cancel) events are emitted.

The ledger plugin MUST authenticate the source for all incoming transfers, whether they include money or not.

If the event is `outgoing_prepare`, then it means you prepared the transfer. `incoming_prepare` means someone prepared
a transfer to you.

### Event: `*_fulfill`
<code style="">ledgerPlugin.on('outgoing_fulfill',
  (
    **transfer**:[Transfer](#class-transfer),
    **fulfillment**:String
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer with a condition is fulfilled. The `fulfillment` is provided as a base64url-encoded string.

This indicates that funds have been transferred. In order to prevent unexpected incoming funds, a ledger MAY forbid
accounts from fulfilling a transfer who are not the transfer's receiver.

If the event is `incoming_fulfill`, then it means you fulfilled the transfer. `outgoing_fulfill` means the receiver
of your outgoing transfer has fulfilled the condition.

### Event: `*_reject`
<code style="">ledgerPlugin.on('outgoing_reject',
  (
    **transfer**:[Transfer](#class-transfer),
    **reason**:[RejectionMessage](#class-rejectionmessage)
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer is rejected by the receiver.

This indicates that a transfer has been manually cancelled before the timeout
by the receiver. A message can be passed along with the rejection.

If the event is `incoming_reject`, then it means you rejected the transfer. `outgoing_reject` means that
the receiver of your outgoing transfer has rejected it.

### Event: `*_cancel`
<code style="">ledgerPlugin.on('outgoing_cancel',
  (
    **transfer**:[Transfer](#class-transfer),
    **reason**:[RejectionMessage](#class-rejectionmessage)
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer is rejected by the ledger.

This will happen on a timeout, triggered by the ledger and not by the receiver.

If the event is `incoming_cancel`, an incoming transfer was timed out by the ledger. `outgoing_cancel`
means that a transfer you created has timed out.

### Event: `incoming_message`
<code style="">ledgerPlugin.on('incoming_message',
  (
    **message**:[IncomingMessage](#incomingmessage),
  ) ⇒
)</code>

Emitted when an incoming message arrives from the ledger.

### Event: `info_change`
<code style="">ledgerPlugin.on('info_change',
  (
    **info**:[LedgerInfo](#class-ledgerinfo)
  ) ⇒
)</code>

Emitted any time the plugin's `LedgerInfo` cache changes.

## Class: Transfer
<code>class Transfer</code>

The `Transfer` class is used to describe local ledger transfers. Fields can be
left undefined (but not any other false-y value) if unused.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [id](#id) | UUID used as an external identifier |
| `String` | [account](#account) | ILP Address of the source or destination account (deprecated) |
| `String` | [from](#from) | ILP Address of the source account |
| `String` | [to](#to) | ILP Address of the destination account |
| `String` | [ledger](#ledger) | ILP Address prefix of the ledger |
| `String` | [amount](#amount) | Integer transfer amount, in the ledger's base unit |
| `String` | [ilp](#ilp) | Base64-encoded ILP packet |
| `Object` | [noteToSelf](#notetoself) | Host-provided memo that should be stored with the transfer |
| `String` | [executionCondition](#executioncondition) | Cryptographic hold condition |
| `String` | [expiresAt](#expiresat) | Expiry time of the cryptographic hold |
| `Object` | [custom](#custom) | Object containing ledger plugin specific options |


### IncomingTransfer
<code>class IncomingTransfer extends [Transfer](#class-transfer)</code>

`IncomingTransfer` objects describe transfers which are **received** by the ledger plugin. The `account` field refers to the local source account that the transfer originated from.

See [`Transfer`](#class-transfer) for more information.

### OutgoingTransfer
<code>class OutgoingTransfer extends [Transfer](#class-transfer)</code>

`OutgoingTransfer` objects describe transfers which have been **sent** by the ledger plugin. The `account` field refers to the local destination account on the underlying ledger.

See [`Transfer`](#class-transfer) for more information.

### Fields

#### id
<code>**id**:String</code>

External unique identifier used by the host.

For [`OutgoingTransfer`](#outgoingtransfer)s, the ID is chosen by the host. The ledger plugin MAY use a different identifier internally, but MUST fail if the external ID has already been used. In the case of a connector, the ID will be deterministically chosen from the hash of the ledger and transfer IDs of the inbound transfer that triggered this outbound transfer.

For [`IncomingTransfer`](#incomingtransfer)s, the ID is chosen by the ledger plugin. The ledger plugin MAY use any type of UUID, but MUST ensure that the same transfer is always referred to by the same ID and that IDs are unique per ledger.

Ledger plugins that support scalability (e.g. running multiple instances of a connector using the same settings) MUST ensure that external transfer IDs are unique **globally**, i.e. across all machines and instances. Otherwise a connector could accidentally process two outgoing payments for one incoming payment.

#### account
<code>**account**:String</code>

The ILP Address of a local account.

**Deprecated:** Use [`from`](#from)/[`to`](#to) instead.

#### from
<code>**from**:String</code>

The ILP Address of the source or debit account.

#### to
<code>**to**:String</code>

The ILP Address of the destination or credit account.

#### ledger
 <code>**ledger**:String</code>

ILP Address prefix of the ledger that this transfer is going through on.

#### amount
<code>**amount**:String</code>

An integer amount, represented as a string of base-ten digits. MUST be `>= 0` and `< 2^64`.

#### ilp
<code>**ilp**:String</code>

An [ILP packet](../0003-interledger-protocol/), denoting the payment's final destination.

#### noteToSelf
<code>**noteToSelf**:Object</code>

An arbitrary plain JavaScript object containing details the host needs to persist with the transfer in order to be able to react to transfer events like condition fulfillment later.

Ledger plugins MAY attach the `noteToSelf` to the transfer and let the ledger store it. Otherwise it MAY use the [`store`](#store) in order to persist this field. Regardless of the implementation, the ledger plugin MUST ensure that all instances of the transfer carry the same `noteToSelf`, even across different machines.

Ledger plugins MUST ensure that the data in the `noteToSelf` either isn't shared with any untrusted party or encrypted before it is shared.

#### executionCondition
<code>**executionCondition**:String</code>

A cryptographic challenge used for implementing holds. The underlying ledger MUST hold the transfer until the condition has been fulfilled or the `expiresAt` time has been reached.

Conditions are the base64url-encoded SHA-256 hash of a random, pseudo-random or deterministically generated 32-byte preimage called the fulfillment.

Ledger plugins that do not support holds MUST reject with an `HoldsNotSupportedError` if this parameter is provided.

#### expiresAt
<code>**expiresAt**:String</code>

An ISO 8601 timestamp representing the expiry date for the transfer.

Ledger plugins that do not support holds or do not support expiries MUST reject with an `ExpiryNotSupportedError` if this parameter is provided.

#### custom
<code>**custom**:Object</code>

Ledger plugins MAY use this object to accept and/or set additional fields for other features they support. The object MUST be serializable, i.e. only plain JSON types are allowed anywhere in the object or sub-objects.

###### Example
``` js
{
  id: '94adc29e-26cd-471b-987e-8d41e8773864',
  account: 'example.ledger.bob',
  from: 'example.ledger.bob',
  to: 'example.ledger.alice',
  ledger: 'example.ledger.',
  amount: '100',
  noteToSelf: /* ... */,
  custom: {
    alternateAccount: 'bob-savings',
    executionPriority: 9
  }
}
```

## Class: Message
<code>class Message</code>

The `Message` class is used to describe local ledger message. All fields are required.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | account | ILP Address of the source or destination account (deprecated) |
| `String` | from | ILP Address of the source account |
| `String` | to | ILP Address of the destination account |
| `String` | ledger | ILP Address prefix of the ledger |
| `Object` | data | Data packet to be sent with the message |

### IncomingMessage
<code>class IncomingMessage extends [Message](#class-message)</code>

`IncomingMessage` objects describe messages which are **received** by the ledger plugin. The `account` field refers to the local source account that the message originated from.

See [`Message`](#class-message) for more information.

### OutgoingMessage
<code>class OutgoingMessage extends [Message](#class-message)</code>

`OutgoingMessage` objects describe messages which have been **sent** by the ledger plugin. The `account` field refers to the local destination account on the underlying ledger.

See [`Message`](#class-message) for more information.

#### account
<code>**account**:String</code>

The ILP Address of a local account.

**Deprecated:** Use [`from`](#from)/[`to`](#to) instead.

#### from
<code>**from**:String</code>

The ILP Address of the source or debit account.

#### to
<code>**to**:String</code>

The ILP Address of the destination or credit account.

#### ledger
<code>**to**:String</code>

The ILP Prefix of the ledger being used to transfer the message.

#### data
<code>**data**:Object</code>

An arbitrary plain JavaScript object containing the data to be sent. The object MUST be serializable to JSON. Ledger plugins SHOULD treat this data as opaque.

If the `data` is too large, the ledger plugin MUST reject with a `MaximumDataSizeExceededError`.

###### Example
``` js
{
  account: 'example.ledger.bob',
  from: 'example.ledger.alice',
  to: 'example.ledger.bob',
  ledger: 'example.ledger.',
  data: { /* ... */ }
}
```

## Class: LedgerInfo
<code>class LedgerInfo</code>

Metadata describing the ledger. This data is returned by the [`getInfo`](#getinfo) method.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [prefix](#prefix) | The plugin's ILP address prefix |
| `String` | [currencyCode](#currencycode) | [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) three-letter currency code |
| `Number` | [currencyScale](#currencyscale) | Integer `(..., -2, -1, 0, 1, 2, ...)`, such that one of the ledger's base units equals `10^-<currencyScale> <currencyCode>` |
| `String[]` | [connectors](#connectors) | ILP addresses of recommended connectors |
| `String` | [minBalance](#minbalance-optional) | Integer String, for instance `"0"`, indicating the minimum balance. Optional, defaults to zero. |
| `String` | [maxBalance](#maxbalance-optional) | Integer String, for instance `"1000000000000"`, indicating the maximum balance. Optional, defaults to plus infinity. |

### Fields

#### prefix
<code>**prefix**:String</code>

The ledger plugin's ILP address prefix. This is used to determine whether a given ILP address is local to this ledger plugin and thus can be reached using this plugin's `sendTransfer` method.

The prefix may be configured, automatically detected, or hard-coded, depending on the ledger. For example, a Bitcoin ledger plugin may have the address hard-coded, while a [`five-bells-ledger`](https://github.com/interledger/five-bells-ledger) would use an API call to get the prefix.

#### currencyCode
<code>**currencyCode**:String</code>

The [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) currency code (if any) used by the ledger. A custom all-caps three-letter code, not used by ISO 4217, otherwise.
Ledger administrators who choose a custom currency code MAY request a custom currency symbol for their chosen currency code be listed by software modules that map currency codes to currency symbols,
for instance on node package manager (npm) in the case of JavaScript.
To translate an integer amount or balance from the ledger, the currencyCode by itself is not enough. It has to be used in combination with the currencyScale (below) to determine how many
of the ledger's base units correspond to one currency unit.

#### currencyScale
<code>**currencyScale**:String</code>

The order of magnitude to express one full currency unit in ledger's base units. For instance, if the integer values represented on the ledger are to be interpreted as
dollar-cents (for the purpose of settling a user's account balance, for instance), then the ledger's
currencyCode is `USD` and its currencyScale is `2`.

#### connectors
<code>**connectors**:String[]</code>

The ILP addresses of recommended connectors.

#### minBalance (OPTIONAL)
<code>**minBalance**:String</code>

A minimum balance limits how much the ledger trusts the account holder.
This field is optional; when not present, the minimum balance should be assumed to be `0`.
When a plugin does return a `minBalance` field, it should be an Integer String, measured in the ledger's base unit,
comparable to the `balance` Integer Strings for which the `getBalance` method returns a Promise.
Applications using the plugin can expect transfers to fail if they would make the balance go below the minimum.

#### maxBalance (OPTIONAL)
<code>**maxBalance**:String</code>

A maximum balance limits how much the account holder trusts the ledger.
This field is optional; when not present, the maximum balance should be assumed to be `+Infinity`.
When a plugin does return a `maxBalance` field, it should be an Integer String, measured in the ledger's base unit,
comparable to the `balance` Integer Strings for which the `getBalance` method returns a Promise.
Applications using the plugin can expect transfers to fail if they would make the balance exceed the maximum.

## Class: PluginOptions
<code>class PluginOptions</code>

Plugin options are passed in to the [`LedgerPlugin`](#class-ledgerplugin)
constructor when a plugin is being instantiated. The fields are ledger
specific. Any fields which cannot be represented as strings are preceded with
an underscore, and listed in the table below.

###### Special Fields
| Type | Name | Description |
|:--|:--|:--|
| `Object` | [_store](#_store) | Persistence layer callbacks |

### Fields

#### _store
<code>**_store**:Object</code>

Provides callback hooks to the host's persistence layer.

Persistence MAY be required for internal use by some ledger plugins. For this purpose hosts MAY be configured with a persistence layer.

Method names are based on the popular LevelUP/LevelDOWN packages.

###### Example
```js
{
  // Store a value under a key
  put: (key, value) => {
    // Returns Promise.<null>
  },
  // Fetch a value by key
  get: (key) => {
    // Returns Promise.<Object>
  },
  // Delete a value by key
  del: (key) => {
    // Returns Promise.<null>
  }
}
```

## Class: ConnectOptions
<code>class ConnectOptions</code>

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `Number` | timeout | milliseconds |

### Fields

#### id
<code>**timeout**:Number</code>

The number of milliseconds that the plugin should spend trying to connect before giving up.

If falsy, use the plugin's default timeout.
If `Infinity`, there is no timeout.

## Class: RejectionMessage
<code>class RejectionMessage</code>

###### Fields
| Field             | Type        | Description |
|:------------------|:------------|:------------|
| `code`            | String      | Machine-readable error code |
| `name`            | String      | Human-readable description of the error code |
| `message`         | String      | Description of the error |
| `triggered_by`    | ILP Address or ILP Prefix | ILP address or ledger prefix from which the rejection originates |
| `forwarded_by`    | ILP Address | (optional) The address of the last connector to forward the rejection |
| `triggered_at`    | Timestamp   | (optional) The time the rejection occurred. |
| `additional_info` | Object      | Additional details about the error |
