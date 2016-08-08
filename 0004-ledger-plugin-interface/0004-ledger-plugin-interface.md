# Ledger Plugin Interface

The Interledger Protocol is a protocol suite for connecting blockchains and other ledgers.

This spec defines a ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP spec](../0003-interledger-protocol/).

## Class: LedgerPlugin
`class LedgerPlugin`

###### Methods
| | Name |
|:--|:--|
| `new` | [**LedgerPlugin**](#new-ledgerplugin) ( opts ) |
| | [**connect**](#connect) ( ) `⇒ Promise.<null>` |
| | [**disconnect**](#disconnect) ( ) `⇒ Promise.<null>` |
| | [**isConnected**](#isconnected) ( ) `⇒ Boolean` |
| | [**getInfo**](#getinfo) ( ) <code>⇒ Promise.&lt;[LedgerInfo](#class-ledgerinfo)></code> |
| | [**getPrefix**](#getprefix) ( ) `⇒ Promise<String>` |
| | [**getAccount**](#getaccount) ( ) `⇒ Promise<String>` |
| | [**getBalance**](#getbalance) ( ) <code>⇒ Promise.&lt;String></code> |
| | [**send**](#send) ( transfer ) <code>⇒ Promise.&lt;null></code> |
| | [**fulfillCondition**](#fulfillcondition) ( transferId, fulfillment ) <code>⇒ Promise.&lt;null></code> |
| | [**replyToTransfer**](#replytotransfer) ( transferId, replyMessage ) <code>⇒ Promise.&lt;null></code> |
| | [**rejectIncomingTransfer**](#rejectincomingtransfer) ( transferId, rejectMessage ) <code>⇒ Promise.&lt;null></code> |

###### Events
| Name | Handler |
|:--|:--|
| [**connect**](#event-connect-) | `( ) ⇒` |
| [**disconnect**](#event-disconnect-) | `( ) ⇒` |
| [**error**](#event-error-) | `( ) ⇒` |
| [**incoming_transfer**](#event-*_transfer-) | <code>( transfer:[IncomingTransfer](#incomingtransfer) ) ⇒</code> |
| [**incoming_prepare**](#event-*_prepare-) | <code>( transfer:[IncomingTransfer](#incomingtransfer) ) ⇒</code> |
| [**incoming_fulfill**](#event-*_fulfill-) | <code>( transfer:[IncomingTransfer](#incomingtransfer), fulfillment:Buffer ) ⇒</code> |
| [**incoming_reject**](#event-*_reject-) | <code>( transfer:[IncomingTransfer](#incomingtransfer), rejectionReason:Buffer ) ⇒</code> |
| [**incoming_cancel**](#event-*_cancel-) | <code>( transfer:[IncomingTransfer](#incomingtransfer), cancellationReason:Buffer ) ⇒</code> |
| [**outgoing_transfer**](#event-*_transfer-) | <code>( transfer:[outgoingTransfer](#outgoingtransfer) ) ⇒</code> |
| [**outgoing_prepare**](#event-*_prepare-) | <code>( transfer:[outgoingTransfer](#outgoingtransfer) ) ⇒</code> |
| [**outgoing_fulfill**](#event-*_fulfill-) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), fulfillment:Buffer ) ⇒</code> |
| [**outgoing_reject**](#event-*_reject-) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), rejectionReason:Buffer ) ⇒</code> |
| [**outgoing_cancel**](#event-*_cancel-) | <code>( transfer:[outgoingTransfer](#outgoingtransfer), cancellationReason:Buffer ) ⇒</code> |

### Instance Management

#### new LedgerPlugin
<code>new LedgerPlugin( **opts** : [PluginOptions](#class-pluginoptions) )</code>

Create a new instance of the plugin. Each instance typically corresponds to a different ledger. However, some plugins MAY deviate from a strict one-to-one relationship and MAY use one instance for multiple (similar) ledgers or multiple instances to talk to the same ledger.

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
<code>ledgerPlugin.connect() ⇒ Promise.&lt;null></code>

Initiate ledger event subscriptions. Once `connect` is called the ledger plugin MUST attempt to subscribe to and report ledger events. Once the connection is established, the ledger plugin should emit the [`connect`](#event-connect-) event. If the connection is lost, the ledger plugin SHOULD emit the [`disconnect`](#event-disconnect-) event.

#### disconnect
<code>ledgerPlugin.disconnect() ⇒ Promise.&lt;null></code>

Unsubscribe from ledger events.

#### isConnected
<code>ledgerPlugin.isConnected() ⇒ Boolean</code>

Query whether the plugin is currently connected.

#### getInfo
<code>ledgerPlugin.getInfo() ⇒ Promise.&lt;[LedgerInfo](#class-ledgerinfo)></code>

Retrieve some metadata about the ledger. Plugin must be connected, otherwise the promise should reject.

###### Example Return Value
```json
{
  "precision": 10,
  "scale": 4,
  "currencyCode": "USD",
  "currencySymbol": "$"
}
```

For a detailed description of these properties, please see [`LedgerInfo`](#class-ledgerinfo).

#### getPrefix
<code>ledgerPlugin.getPrefix() ⇒ Promise.&lt;String></code>

Get the ledger plugin's ILP address prefix. This is used to determine whether a given ILP address is local to this ledger plugin and thus can be reached using this plugin's `send` method.

The prefix may be configured, automatically detected, or hard-coded, depending on the ledger. For example, a Bitcoin ledger plugin may have the address hard-coded, while a [`five-bells-ledger`](https://github.com/interledger/five-bells-ledger) would use an API call to get the prefix.

###### Example Return Value
`us.fed.some-bank`

#### getAccount
<code>ledgerPlugin.getAccount() ⇒ Promise.&lt;String></code>

Get the ledger plugin's ILP address. This is given to senders to receive transfers to this account.

The mapping from the ILP address to the local ledger address is dependent on the ledger / ledger plugin. An ILP address could be the `<ledger prefix>.<account name or number>`, or a token could be used in place of the actual account name or number.

###### Example Return Value
`us.fed.some-bank.my-account`

#### getBalance
<code>ledgerPlugin.getBalance() ⇒ Promise.&lt;String></code>

Return a decimal string representing the current balance. Plugin must be connected, otherwise the promise should reject.

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

#### send
<code>ledgerPlugin.send( **transfer**:[OutgoingTransfer](#outgoingtransfer) ) ⇒ Promise.&lt;null></code>

Plugin must be connected, otherwise the promise should reject. Initiates a ledger-local transfer. A transfer can
contain money and/or information. If there is a problem with the structure or
validity of the transfer, then `send` should throw an error in the form of a
rejected promise. If the transfer is accepted by the ledger, however, then
further errors will be in the form of `"reject"` events.

All plugins MUST implement zero-amount transfers, but some ledger plugins MAY
implement zero-amount transfers differently than other transfers.

###### Parameters
| Name | Type | Description |
|:--|:--|:--|
| transfer | <code>[OutgoingTransfer](#outgoingtransfer)</code> | Properties of the transfer to be created |

###### Returns
**`Promise.<null>`** A promise which resolves when the transfer has been submitted (but not necessarily accepted.)

###### Example
```js
p.send({
  id: 'd86b0299-e2fa-4713-833a-96a6a75271b8',
  account: 'example.ledger.connector',
  amount: '10',
  data: new Buffer('...', 'base64'),
  noteToSelf: {},
  executionCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0',
  expiresAt: '2016-05-18T12:00:00.000Z'
})
```

For a detailed description of these properties, please see [`OutgoingTransfer`](#outgoingtransfer).

#### fulfillCondition
<code>ledgerPlugin.fulfillCondition( **transferId**:String, **fulfillment**:Buffer ) ⇒ Promise.&lt;null></code>

Submit a fulfillment to a ledger. Plugin must be connected, otherwise the promise should reject.

#### replyToTransfer
<code>ledgerPlugin.replyToTransfer( **transferId**:String, **replyMessage**:Buffer ) ⇒ Promise.&lt;null></code>

**TODO**: Define what the message format is.  Plugin must be connected, otherwise the promise should reject.

#### rejectIncomingTransfer
<code>ledgerPlugin.rejectIncomingTransfer( **transferId**:String, **rejectMessage**:Buffer ) ⇒ Promise.&lt;null></code>

Reject an incoming transfer that is held pending the fulfillment of its `executionCondition` before the `expiresAt` time. `rejectMessage` MAY be supplied to provide details on why the transfer was rejected.

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

Note that the `*_prepare` event **DOES NOT** indicate that money has been transferred. The final status will only be known when either the [*_fulfill](#event-*_fulfill-) or [*_cancel](#event-*_cancel-) events are emitted.

The ledger plugin MUST authenticate the source for all incoming transfers, whether they include money or not.

If the event is `outgoing_prepare`, then it means you prepared the transfer. `incoming_prepare` means someone prepared
a transfer to you.

### Event: `*_fulfill`
<code style="">ledgerPlugin.on('outgoing_fulfill',
  (
    **transfer**:[Transfer](#class-transfer),
    **fulfillment**:Buffer
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer with a condition is fulfilled.

This indicates that funds have been transferred. In order to prevent unexpected incoming funds, a ledger MAY forbid
accounts from fulfilling a transfer who are not the transfer's receiver.

If the event is `incoming_fulfill`, then it means you fulfilled the transfer. `outgoing_fulfill` means the receiver
of your outgoing transfer has fulfilled the condition.

### Event: `*_reject`
<code style="">ledgerPlugin.on('outgoing_reject',
  (
    **transfer**:[Transfer](#class-transfer),
    **reason**:Buffer
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
    **reason**:Buffer
  ) ⇒
)</code>

Emitted when an outgoing/incoming transfer is rejected by the ledger.

This will happen on a timeout, triggered by the ledger and not by the receiver.

If the event is `incoming_cancel`, an incoming transfer was timed out by the ledger. `outgoing_cancel`
means that a transfer you created has timed out.

## Class: Transfer
<code>class Transfer</code>

The `Transfer` class is used to describe local ledger transfers. Only
[id](#id), [account](#account), [ledger](#ledger), and [amount](#amount) are required; the other
fields can be left undefined (but not any other false-y value) if unused.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [id](#id) | UUID used as an external identifier |
| `String` | [account](#account) | ILP Address of the source or destination account |
| `String` | [ledger](#ledger) | ILP Address prefix of the ledger |
| `String` | [amount](#amount) | Decimal transfer amount |
| `Buffer` | [data](#data) | Data packet or memo to be sent with the transfer, starts with an ILP header |
| `Buffer` | [noteToSelf](#notetoself) | Host-provided memo that should be stored with the transfer |
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

#### ledger
 <code>**ledger**:String</code>

ILP Address prefix of the ledger that this transfer is going through on.

#### amount
<code>**amount**:String</code>

A decimal amount, represented as a string. MUST be positive. The supported precision is defined by each ledger plugin and can be queried by the host via [`getInfo`](#getinfo). The ledger plugin MUST throw an `InsufficientPrecisionError` if the given amount exceeds the supported level of precision.

#### data
<code>**data**:Buffer</code>

A buffer containing the data to be sent. Ledger plugins SHOULD treat this data as opaque, however it will usually start with an [ILP header](../0003-interledger-protocol/) followed by a transport layer header, a [quote request](../0008-interledger-quoting-protocol/) or a custom user-provided data packet.

If the `data` is too large, the ledger plugin MUST throw a `MaximumDataSizeExceededError`. If the `data` is too large only because the `amount` is insufficient, the ledger plugin MUST throw an `InsufficientAmountError`.

#### noteToSelf
<code>**noteToSelf**:Buffer</code>

An optional bytestring containing details the host needs to persist with the transfer in order to be able to react to transfer events like condition fulfillment later.

Ledger plugins MAY attach the `noteToSelf` to the transfer and let the ledger store it. Otherwise it MAY use the [`store`](#store) in order to persist this field. Regardless of the implementation, the ledger plugin MUST ensure that all instances of the transfer carry the same `noteToSelf`, even across different machines.

Ledger plugins MUST ensure that the data in the `noteToSelf` either isn't shared with any untrusted party or encrypted before it is shared.

#### executionCondition
<code>**executionCondition**:String</code>

A [cryptographic condition](../0002-crypto-conditions/) used for implementing holds. The underlying ledger MUST hold the transfer until the condition has been fulfilled or the `expiresAt` time has been reached.

Ledger plugins that do not support holds MUST throw an `HoldsNotSupportedError` if this parameter is provided.

Ledger plugins that do support holds, but do not support the given condition type or bitmask MUST throw a  `ExecutionConditionNotSupportedError`.

#### expiresAt
<code>**expiresAt**:String</code>

An ISO 8601 timestamp representing the expiry date for the transfer.

Ledger plugins that do not support holds or do not support expiries MUST throw an `ExpiryNotSupportedError` if this parameter is provided.

#### custom
<code>**custom**:Object</code>

Ledger plugins MAY use this object to accept and/or set additional fields for other features they support. The object MUST be serializable, i.e. only plain JSON types are allowed anywhere in the object or sub-objects.

###### Example
``` js
{
  id: '94adc29e-26cd-471b-987e-8d41e8773864',
  account: 'example.ledger.bob',
  ledger: 'example.ledger.',
  amount: '100',
  data: /* ... */,
  noteToSelf: /* ... */,
  custom: {
    alternateAccount: 'bob-savings',
    executionPriority: 9
  }
}
```

## Class: LedgerInfo
<code>class LedgerInfo</code>

Metadata describing the ledger. This data is returned by the [`getInfo`](#getinfo) method.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `Number` | [precision](#precision) | Total number of digits allowed |
| `Number` | [scale](#scale) | Digits allowed after decimal |
| `String` | [currencyCode](#currencycode) | ISO three-letter currency code |
| `String` | [currencySymbol](#currencysymbol) | UTF8 currency symbol |

### Fields

#### precision
<code>**precision**:Number</code>

The total number of digits (base 10) of precision allowed by the ledger.

#### scale
<code>**scale**:Number</code>

The number of digits allowed after the decimal point.

#### currencyCode
<code>**currencyCode**:String</code>

The ISO 4217 currency code (if any) used by the ledger.

#### currencySymbol
<code>**currencySymbol**:String</code>

The currency symbol as one or more UTF8 characters.

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
