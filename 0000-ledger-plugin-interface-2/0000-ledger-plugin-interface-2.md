---
title: The Javascript Ledger Plugin Interface Version 2
draft: 1
---
# Javascript Ledger Plugin Interface Version 2

The Interledger Protocol is a protocol suite for making payments across multiple different settlement systems.

This spec defines a Javascript ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols. While the exact methods and events defined here are specific to the Javascript implementation, this may be used as a guide for ledger abstractions in other languages.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP spec](../0003-interledger-protocol/).

## Class: LedgerPlugin
`class LedgerPlugin`

###### Methods
| | Name |
|:--|:--|
| `new` | [**LedgerPlugin**](#new-ledgerplugin) ( opts ) |
| | [**connect**](#ledgerpluginconnect) ( options ) `⇒ Promise.<null>` |
| | [**disconnect**](#ledgerplugindisconnect) ( ) `⇒ Promise.<null>` |
| | [**isConnected**](#ledgerpluginisconnected) ( ) `⇒ Boolean` |
| | [**getInfo**](#ledgerplugingetinfo) ( ) <code>⇒ [LedgerInfo](#class-ledgerinfo)</code> |
| | [**sendTransfer**](#ledgerpluginsendtransfer) ( transfer ) <code>⇒ Promise.&lt;[FulfillmentInfo](#class-fulfillmentinfo)></code> |
| | [**registerTransferHandler**](#ledgerpluginregistertransferhandler) ( transferHandler ) <code>⇒ null</code> |
| | [**deregisterTransferHandler**](#ledgerpluginderegistertransferhandler) ( ) <code>⇒ null</code> |

###### Constants

| | Name |
|:--|:--|
| `static` | [**version**](#ledgerpluginversion) = 2 |

###### Events
| Name | Handler |
|:--|:--|
| [**connect**](#event-connect) | `( ) ⇒` |
| [**disconnect**](#event-disconnect) | `( ) ⇒` |
| [**error**](#event-error) | `( ) ⇒` |

###### Errors
| Name | Description |
|:--|:--|
| [**InvalidFieldsError**]() | Arguments or configuration were invalidated client-side |
| [**UnreachableError**]() | An error occured due to connection failure |
| [**NotAcceptedError**]() | An operation has been rejected due to ledger-side logic |
| [**NoSubscriptionsError**]() | A transfer cannot be delivered because there are no active websockets |

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

#### LedgerPlugin.version
<code>LedgerPlugin.**version**:Number</code>

Always `2` for this version of the Ledger Plugin Interface.

### Connection Management

#### LedgerPlugin#connect
<code>ledgerPlugin.connect( options:[ConnectOptions](#class-connectoptions ) ⇒ Promise.&lt;null></code>

`options` is optional.

Initiate ledger event subscriptions. Once `connect` is called the ledger plugin MUST attempt to subscribe to and report ledger events. Once the connection is established, the ledger plugin should emit the [`connect`](#event-connect-) event. If the connection is lost, the ledger plugin SHOULD emit the [`disconnect`](#event-disconnect-) event. The plugin should ensure that the information returned by `getInfo` is available and cached before emitting the [`connect`](#event-connect-) event.

Rejects with `InvalidFieldsError` if credentials are missing, and `NotAcceptedError` if credentials are rejected.
Rejects with `TypeError` if `options.timeout` is passed but is not a `Number`.

#### LedgerPlugin#disconnect
<code>ledgerPlugin.disconnect() ⇒ Promise.&lt;null></code>

Unsubscribe from ledger events.

#### LedgerPlugin#isConnected
<code>ledgerPlugin.isConnected() ⇒ Boolean</code>

Query whether the plugin is currently connected.

#### LedgerPlugin#getInfo
<code>ledgerPlugin.getInfo() ⇒ [LedgerInfo](#class-ledgerinfo)</code>

Retrieve some metadata about the ledger. Throws `NotConnectedError` if the plugin is not connected to the ledger.

###### Example Return Value
```json
{
  "currencyCode": "USD",
  "currencyScale": 4
}
```

For a detailed description of these properties, please see [`LedgerInfo`](#class-ledgerinfo).

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

#### LedgerPlugin#sendTransfer
<code>ledgerPlugin.sendTransfer( **transfer**:[Transfer](#class-transfer) ) ⇒ Promise.&lt;[FulfillmentInfo](#class-fulfillmentinfo)></code>

Initiates an account-local transfer. A transfer MUST contain an `amount` of zero or more and MAY have attached `ilp` data. See the description of the [Transfer](#class-transfer) class below.

All plugins MUST support amounts in a range from zero to some maximum. Plugins MAY implement zero-amount transfers differently than other transfers.

###### Parameters
| Name | Type | Description |
|:--|:--|:--|
| transfer | <code>[Transfer](#class-transfer)</code> | Properties of the transfer to be created |

When sending transfers, all fields are required and MUST be provided, even if they contain an empty value, such as an empty object in `custom`.

###### Returns
**`Promise.<FulfillmentInfo>`** A promise which resolves when the transfer has been fulfilled/executed.

Rejects with `InvalidFieldsError` if required fields are missing from the transfer or malformed. Rejects with `NotAcceptedError` if the transfer is rejected by the ledger due to insufficient balance or any other reason. Rejects with `NotConnectedError` if the plugin is not connected to the ledger.

Rejects with [`InterledgerRejectionError`](#class-interledgerrejectionerror) if the other side rejects the transfer and attaches ILP rejection data. Rejects with `GenericRejectionError` if the other side rejects the transfer, but does not attach valid ILP rejection data.

This method MAY reject with any arbitrary JavaScript error.

###### Example
```js
p.sendTransfer({
  amount: '10',
  executionCondition: '47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU',
  expiresAt: '2016-05-18T12:00:00.000Z',
  ilp: Buffer.alloc(0),
  custom: {}
})
```

For a detailed description of these properties, please see [`Class: Transfer`](#class-transfer).

#### LedgerPlugin#registerTransferHandler
<code>ledgerPlugin.registerTransferHandler( **transferHandler**: ( transfer: [Transfer](#class-transfer) ) ⇒ Promise&lt;[FulfillmentInfo](#class-fulfillmentinfo)> ) ⇒ null</code>

Set the callback which is used to handle incoming prepared transfers. The callback should expect one parameter (the [Transfer](#class-transfer)) and return a promise for the resulting [FulfillmentInfo](#class-fulfillmentinfo). If the transfer is rejected or an error occurs, the callback should reject the transfer. In general, the callback should behave as [`sendTransfer`](#ledgerpluginsendtransfer) does.

If a transfer handler is already set, this method throws a `TransferHandlerAlreadyRegisteredError`. In order to change the transfer handler, the old handler must first be removed via [`deregisterTransferHandler`](#ledgerpluginderegistertransferhandler). This is to ensure that handlers are not overwritten by accident.

If an incoming transfer is received by the plugin, but no handler is registered, the plugin should reject the transfer.

#### LedgerPlugin#deregisterTransferHandler
<code>ledgerPlugin.deregisterTransferHandler( ) ⇒ null</code>

Removes the currently used transfer handler. This has the same effect as if [`registerTransferHandler`](#ledgerpluginregistertransferhandler) had never been called.

If no transfer handler is currently set, this method does nothing.

## Class: Transfer
<code>class Transfer</code>

The `Transfer` class is used to describe transfers from the originator of the sendTransfer call towards some destination via Interledger. All fields are required and MUST NOT be undefined. However, `amount` MAY be the value `'0'`, `ilp` MAY be an empty buffer and `custom` MAY be an empty object.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [amount](#transferamount) | Integer transfer amount, in the ledger's base unit |
| `Buffer` | [ilp](#transferilp) | Attached data (ILP packet) |
| `String` | [executionCondition](#transferexecutioncondition) | Cryptographic hold condition |
| `String` | [expiresAt](#transferexpiresat) | Expiry time of the cryptographic hold |
| `Object` | [custom](#transfercustom) | Object containing ledger plugin specific options |

###### Example
``` js
{
  amount: '100',
  executionCondition: 'I3TZF5S3n0-07JWH0s8ArsxPmVP6s-0d0SqxR6C3Ifk',
  expiresAt: '2017-12-02T11:51:26.627Z',
  ilp: Buffer.alloc(0),
  custom: {
    _alternateAccount: 'bob-savings',
    executionPriority: 9
  }
}
```

### Fields

#### Transfer#amount
<code>**amount**:String</code>

An integer amount, represented as a string of base-ten digits. MUST be in the range `0..9223372036854775807` (`>= 0` and `< 2^64`).

###### Example

``` js
'100'
```

#### Transfer#ilp
<code>**ilp**:Buffer</code>

An [ILP packet](https://interledger.org/rfcs/0003-interledger-protocol/draft-4.html#specification), denoting the payment's final destination. Plugins SHOULD support a size (in bytes) in the range `0..65535` (`>= 0` and `< 2^16`). Note that ILP packets are currently smaller than that, but larger packets may be used in the future due to extensions.

If the `ilp` data is too large, the ledger plugin MUST reject with a `MaximumIlpDataSizeExceededError`.

#### Transfer#executionCondition
<code>**executionCondition**:String</code>

A cryptographic challenge used for implementing holds. The underlying ledger MUST hold the transfer until the condition has been fulfilled or the `expiresAt` time has been reached.

Conditions are the base64url-encoded SHA-256 hash of a random or pseudo-random 32-byte preimage called the fulfillment.

###### Example

``` js
'I3TZF5S3n0-07JWH0s8ArsxPmVP6s-0d0SqxR6C3Ifk'
```

#### Transfer#expiresAt
<code>**expiresAt**:String</code>

An ISO 8601 datetime string representing the expiry date for the transfer. Must include the UTC timezone identifier `Z`.

This date MUST be in the future, otherwise the plugin MUST reject with a `UnacceptableExpiryError`.

###### Example

``` js
'2017-12-02T11:51:26.627Z'
```

#### Transfer#custom
<code>**custom**:Object</code>

Ledger plugins MAY use this object to accept and/or set additional fields for other features they support. The object MUST be serializable, i.e. only plain JSON types are allowed anywhere in the object or sub-objects.

If the `custom` data is too large, the ledger plugin MUST reject with a `MaximumCustomDataSizeExceededError`.

Note that connectors MAY forward some fields of `custom` data from plugin to plugin, but generally are not expected to. All `custom` fields that were passed to `sendTransfer` MUST be passed to the transfer handler by the plugin on the receiving side. The only exception are properties which start with the underscore character (`_`), which MAY be consumed by the plugin and not passed on.

###### Example
``` js
{
  // Starts with an underscore, consumed by plugin
  _alternateAccount: 'bob-savings',
  // Other property, passed on to next connector/receiver
  executionPriority: 9
}
```

## Class: FulfillmentInfo
<code>class FulfillmentInfo</code>

The `FulfillmentInfo` class is used to describe the fulfillment and associated data that is returned when a transfer successfully completes.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [fulfillment](#fulfillmentinfofulfillment) | Cryptographic hold fulfillment |
| `Buffer` | [ilp](#fulfillmentinfoilp) | Attached data (ILP packet) |
| `Object` | [custom](#fulfillmentinfocustom) | Object containing ledger plugin specific options |

### Fields

#### FulfillmentInfo#fulfillment
<code>**fulfillment**:String</code>

A cryptographic fulfillment that is the SHA-256 preimage of the hash provided as the [`executionCondition`](#transferexecutioncondition) when the transfer was first prepared.

Fulfillments are base64url-encoded values with a length of exactly 32 bytes.

#### FulfillmentInfo#ilp
<code>**ilp**:Buffer</code>

An [ILP packet](https://interledger.org/rfcs/0003-interledger-protocol/draft-4.html#specification), containing any data attached to the fulfillment. Plugins SHOULD support a size (in bytes) in the range `0..65535` (`>= 0` and `< 2^16`). Note that ILP packets are currently smaller than that, but larger packets may be used in the future due to extensions.

#### FulfillmentInfo#custom
<code>**custom**:Object</code>

Ledger plugins MAY use this object to accept and/or set additional fields for other features they support. The object MUST be serializable, i.e. only plain JSON types are allowed anywhere in the object or sub-objects.

Note that connectors MAY forward some fields of `custom` data from plugin to plugin, but generally are not expected to. All `custom` fields that were set in `FulfillmentInfo#custom` on the receiving side MUST be set in `FulfillmentInfo#custom` when it is resolved by the promise on the sending side. The only exception are properties which start with the underscore character (`_`), which MAY be consumed by the plugin and not passed on.

All custom fields that were set in FulfillmentInfo#custom on the receiving side MUST be set in FulfillmentInfo#custom when it is resolved by the promise on the sending side.

###### Example
``` js
{
  custom: {
    claim: '...',
    fulfillmentLatency: 29
  }
}
```

## Class: InterledgerRejectionError
<code>class InterledgerRejectionError</code>

An `InterledgerRejectionError` is a throwable object representing a rejection of an Interledger transfer. Implementations SHOULD use a class named `InterledgerRejectionError` which derives from JavaScript's built-in `Error`. However, other implementations MUST NOT rely on this and SHOULD use the `name` property to distinguish Interledger rejections from other error types.

Plugins SHOULD NOT generally trigger `InterledgerRejectionError`s. Instead, the plugin SHOULD trigger a local error, such as the ones specified in this document and the hosting connector SHOULD create a suitable `InterledgerRejectionError` from the local error. This is because plugins are not necessarily aware of their ILP address and therefore may not be able to set `triggeredBy` correctly. Some plugins may have elements of a connector built-in if they are used with ledgers that don't natively support ILP. In that case, the plugin MAY trigger an `InterledgerRejectionError` since it is in effect acting as a connector.

All fields described below MUST be present, however they MAY be empty.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [name](#interledgerrejectionerrorname) | `'InterledgerRejectionError'` |
| `String` | [message](#interledgerrejectionerrormessage) | Error message for local use |
| `Buffer` | [ilp](#interledgerrejectionerrorilp) | Attached data (ILP packet) |

### Fields

#### InterledgerRejectionError#name
<code>**name**:String</code>

JavaScript error name, always `'InterledgerRejectionError'`. This property SHOULD be used to distinguish InterledgerRejectionErrors from other error types, e.g.:

``` js
try {
  await plugin.sendTransfer(transfer)
} catch (err) [
  if (err && err.name === 'InterledgerRejectionError') {
    // This is an Interledger rejection
  } else {
    // This is some other type of error
  }
]
```

#### InterledgerRejectionError#message
<code>**message**:String</code>

JavaScript error message. This field is generally only used locally and not passed on to other hosts. However, implementations MAY include a `message` property in `additionalInfo` which matches the local error message. Implementers SHOULD take care not to disclose secret keys or other private information via `additionalInfo`.

#### InterledgerRejectionError#ilp
<code>**ilp**:Buffer</code>

An [ILP packet](https://interledger.org/rfcs/0003-interledger-protocol/draft-4.html#specification), containing information on why the payment has been rejected and by whom. Plugins SHOULD support a size (in bytes) in the range `0..65535` (`>= 0` and `< 2^16`). Note that ILP packets are currently smaller than that, but larger packets may be used in the future due to extensions.

## Class: LedgerInfo
<code>class LedgerInfo</code>

Metadata describing the ledger. This data is returned by the [`getInfo`](#getinfo) method.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [currencyCode](#ledgerinfocurrencycode) | [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) three-letter currency code |
| `Number` | [currencyScale](#ledgerinfocurrencyscale) | Integer `(..., -2, -1, 0, 1, 2, ...)`, such that one of the ledger's base units equals `10^-<currencyScale> <currencyCode>` |

### Fields

#### LedgerInfo#currencyCode
<code>**currencyCode**:String</code>

The [ISO 4217](https://en.wikipedia.org/wiki/ISO_4217) currency code (if any) used by the ledger. A custom all-caps three-letter code, not used by ISO 4217, otherwise.
Ledger administrators who choose a custom currency code MAY request a custom currency symbol for their chosen currency code be listed by software modules that map currency codes to currency symbols,
for instance on node package manager (npm) in the case of JavaScript.
To translate an integer amount or balance from the ledger, the currencyCode by itself is not enough. It has to be used in combination with the currencyScale (below) to determine how many
of the ledger's base units correspond to one currency unit.

#### LedgerInfo#currencyScale
<code>**currencyScale**:String</code>

The order of magnitude to express one full currency unit in ledger's base units. For instance, if the integer values represented on the ledger are to be interpreted as
dollar-cents (for the purpose of settling a user's account balance, for instance), then the ledger's
currencyCode is `USD` and its currencyScale is `2`.

## Class: PluginOptions
<code>class PluginOptions</code>

Plugin options are passed in to the [`LedgerPlugin`](#class-ledgerplugin)
constructor when a plugin is being instantiated. The fields are ledger
specific. Any fields which cannot be represented as strings are preceded with
an underscore, and listed in the table below.

###### Special Fields
| Type | Name | Description |
|:--|:--|:--|
| `Object` | [_store](#pluginoptions-_store) | Persistence layer callbacks |

### Fields

#### PluginOptions#_store
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
| `Number` | [timeout](#connectoptions-timeout) | milliseconds |

### Fields

#### ConnectOptions#timeout
<code>**timeout**:Number</code>

The number of milliseconds that the plugin should spend trying to connect before giving up.

If falsy, use the plugin's default timeout.
If `Infinity`, there is no timeout.
