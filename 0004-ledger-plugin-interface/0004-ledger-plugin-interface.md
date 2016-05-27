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
| `static` | [**canConnectToLedger**](#canconnecttoledger) ( auth ) `⇒ Boolean`|
| `new` | [**LedgerPlugin**](#new-ledgerplugin) ( opts ) |
| | [**connect**](#connect) ( ) `⇒ Promise.<null>` |
| | [**disconnect**](#disconnect) ( ) `⇒ Promise.<null>` |
| | [**isConnected**](#isconnected) ( ) `⇒ Boolean` |
| | [**getInfo**](#getinfo) ( ) <code>⇒ Promise.&lt;[LedgerInfo](#class-ledgerinfo)></code> |
| | [**getConnectors**](#getconnectors) ( ) <code>⇒ Promise.&lt;Array.&lt;String>></code> |
| | [**send**](#send) ( ) <code>⇒ Promise.&lt;null></code> |
| | [**fulfillCondition**](#fulfillcondition) ( transferId, fulfillment ) <code>⇒ Promise.&lt;null></code> |
| | [**replyToTransfer**](#replytotransfer) ( transferId, replyMessage ) <code>⇒ Promise.&lt;null></code> |

###### Events
| Name | Handler |
|:--|:--|
| [**connect**](#event-connect-) | `( ) ⇒` |
| [**disconnect**](#event-disconnect-) | `( ) ⇒` |
| [**error**](#event-error-) | `( ) ⇒` |
| [**incoming**](#event-incoming-) | <code>( transfer:[IncomingTransfer](#incomingtransfer) ) ⇒</code> |
| [**fulfill_execution_condition**](#event-fulfill_execution_condition-) | <code>( transfer:[Transfer](#class-transfer), fulfillment:Buffer ) ⇒</code> |
| [**fulfill_cancellation_condition**](#event-fulfill_cancellation_condition-) | <code>( transfer:[Transfer](#class-transfer), fulfillment:Buffer ) ⇒</code> |
| [**reject**](#event-reject-) | <code>( transfer:[OutgoingTransfer](#outgoingtransfer), rejectionReason:Buffer ) ⇒</code> |
| [**reply**](#event-reply-) | <code>( transfer:[OutgoingTransfer](#outgoingtransfer), replyMessage:Buffer ) ⇒</code> |

### Instance Management

#### canConnectToLedger
<code>LedgerPlugin.canConnectToLedger( **auth** : Object ) ⇒ Boolean</code>

Returns true if and only if this ledger plugin can connect to the ledger described by the authentication data provided.

Ledger plugins are queried in precedence order and the first plugin that returns true for this method will be used to talk to the given ledger.

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
  auth: {
    // auth parameters are defined by the plugin
  },
  store: {
    // persistence may be required for internal use by some ledger plugins
    // (e.g. when the ledger has reduced memo capability and we can only put an ID in the memo)
    get: function (key) {
      // Returns Promise.<Object>
    },
    set: function (key, value) {
      // Returns Promise.<Object>
    },
    remove: function (key) {
      // Returns Promise.<Object>
    }
  }
})
```

For a detailed description of these properties, please see [`PluginOptions`](#class-pluginoptions).

### Connection Management

#### connect
<code>p.connect() ⇒ Promise.&lt;null></code>

Initiate ledger event subscriptions. Once `connect` is called the ledger plugin MUST attempt to subscribe to and report ledger events. Once the connection is established, the ledger plugin should emit the [`connect`](#event-connect-) event. If the connection is lost, the ledger plugin SHOULD emit the [`disconnect`](#event-disconnect-) event.

#### disconnect
<code>p.disconnect() ⇒ Promise.&lt;null></code>

Unsubscribe from ledger events.

#### isConnected
<code>p.isConnected() ⇒ Boolean</code>

Query whether the plugin is currently connected.

#### getInfo
<code>p.getInfo() ⇒ Promise.&lt;[LedgerInfo](#class-ledgerinfo)></code>

Retrieve some metadata about the ledger.

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

#### getConnectors
<code>p.getConnectors() ⇒ Promise.&lt;Array.&lt;String>></code>

Return an array of opaque local destination identifiers representing neighboring connectors.

#### Event: `connect`
<code>p.on('connect', () ⇒ )</code>

Emitted whenever a connection is successfully established.

#### Event: `disconnect`
<code>p.on('disconnect', () ⇒ )</code>

Emitted when the connection has been terminated or lost.

#### Event: `error`
<code>p.on('error', ( **err**:Error ) ⇒ )</code>

General event for fatal exceptions. Emitted when the plugin experienced an unexpected unrecoverable condition. Once triggered, this instance of the plugin MUST NOT be used anymore.

### Ledger Transfers

Note that all transfers will have `transferId`'s to allow the plugin user to correlate actions related to a single transfer. The `transferId` will be the same as the ID used by the underlying ledger wherever possible or applicable. If the ledger does not have transfer IDs, the plugin may generate one and use the `store` passed in to the constructor to persist them.

#### send
<code>p.send( **transfer**:[OutgoingTransfer]() ) ⇒ Promise.&lt;null></code>

Initiates a ledger-local transfer. A transfer can contain money and/or information.

Some ledger plugins MAY implement zero-amount transfers differently than other transfers.

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
  account: 'https://ledger.example/accounts/connector',
  amount: '10',
  data: new Buffer('...', 'base64'),
  noteToSelf: {},

  // for UTP/ATP support
  executionCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0',

  // for UTP support
  expiresAt: '2016-05-18T12:00:00.000Z',

  // for ATP support
  cancellationCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0'
})
```

For a detailed description of these properties, please see [`OutgoingTransfer`](#outgoingtransfer).

#### fulfillCondition
<code>p.fulfillCondition( **transferId**:String, **fulfillment**:Buffer ) ⇒ Promise.&lt;null></code>

Submit a fulfillment to a ledger. The ledger plugin or the ledger MUST automatically detect whether the fulfillment is an execution or cancellation condition fulfillment.

#### replyToTransfer
<code>p.replyToTransfer( **transferId**:String, **replyMessage**:Buffer ) ⇒ Promise.&lt;null></code>

**TODO**: Define what the message format is

#### Event: `incoming`
<code>p.on('incoming', ( **transfer**:[IncomingTransfer](#incomingtransfer) ) ⇒ )</code>

Emitted when an incoming transfer is received.

The ledger plugin MUST authenticate the source for all incoming transfers, whether they include money or not.

###### Example `transfer`

```js
{
  id: 'https//ledger.example/transfers/123',
  account: 'https://ledger.example/accounts/connector',
  amount: '10',
  data: Buffer(...),
  noteToSelf: {},

  // for UTP/ATP support
  executionCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0',

  // for UTP support
  expiresAt: '2016-05-18T12:00:00.000Z',

  // for ATP support
  cancellationCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0'
}
```

For a detailed description of these properties, please see [`IncomingTransfer`](#incomingtransfer).

#### Event: `fulfill_execution_condition`
<code style="">p.on('fulfill_execution_condition',
  (
    **transfer**:[Transfer](#class-transfer),
    **fulfillment**:Buffer
  ) ⇒
)</code>

Emitted when a transfer's execution condition has been fulfilled.

If the transfer is an [`OutgoingTransfer`](#outgoingtransfer), connectors will forward the execution condition to the corresponding [`IncomingTransfer`](#incomingtransfer).

#### Event: `fulfill_cancellation_condition`
<code style="">p.on('fulfill_cancellation_condition',
  (
    **transfer**:[Transfer](#class-transfer),
    **fulfillment**:Buffer
  ) ⇒
)</code>

Emitted when a transfer's cancellation condition has been fulfilled.

If the transfer is an [`IncomingTransfer`](#incomingtransfer), connectors will forward the execution condition to the corresponding [`OutgoingTransfer`](#outgoingtransfer).

#### Event: `reject`
<code>p.on('reject',
  (
    **transfer**:[OutgoingTransfer](#outgoingtransfer),
    **rejectionReason**:Buffer
  ) ⇒
)</code>

Emitted when the ledger has informed us that our outgoing transfer is not going to happen. The `rejectionReason` is a ledger plugin-specific error.

#### Event: `reply`
<code>p.on('reject',
  (
    **transfer**:[OutgoingTransfer](#outgoingtransfer),
    **replyMessage**:Buffer
  ) ⇒
)</code>

Emitted when the recipient of a local transfer we initiated has sent us a reply related to the transfer, e.g. using [`replyToTransfer`](#replytotransfer). Used for returning errors in the case of a failed payment.

## Class: Transfer
<code>class Transfer</code>

The `Transfer` class is used to describe local ledger transfers.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `String` | [id](#id) | UUID used as an external identifier |
| `String` | [account](#account) | Local source or destination account ID |
| `String` | [amount](#amount) | Decimal transfer amount |
| `Buffer` | [data](#data) | Data packet or memo to be sent with the transfer, starts with an ILP header |
| `Buffer` | [noteToSelf](#notetoself) | Host-provided memo that should be stored with the transfer |
| `String` | [executionCondition](#executioncondition) | Cryptographic hold condition, used in [UTP](../0006-universal-transport-protocol/)/[ATP](../0007-atomic-transport-protocol/) |
| `String` | [cancellationCondition](#cancellationcondition) | Cryptographic abort condition, used in [ATP](../0007-atomic-transport-protocol/) |
| `String` | [expiresAt](#expiresat) | Expiry time of the cryptographic hold, used in [UTP](../0006-universal-transport-protocol/) |
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

A local account identifier. The format for account identifiers is chosen by the ledger plugin. Hosts MUST treat account identifiers as opaque strings.

#### amount
<code>**amount**:String</code>

A decimal amount, represented as a string. MUST be positive. The supported precision is defined by each ledger plugin and can be queried by the host via [`getInfo`](#getinfo). The ledger plugin MUST throw an `InsufficientPrecisionError` if the given amount exceeds the supported level of precision.

#### data
<code>**data**:Buffer</code>

A buffer containing the data to be sent. Ledger plugins SHOULD treat this data as opaque, however it will usually start with an [ILP header](../0003-interledger-protocol/) followed by a transport layer header, a [quote request]() or a custom user-provided data packet.

If the `data` is too large, the ledger plugin MUST throw a `MaximumDataSizeExceededError`. If the `data` is too large only because the `amount` is insufficient, the ledger plugin MUST throw an `InsufficientAmountError`.

#### noteToSelf
<code>**noteToSelf**:Buffer</code>

An optional bytestring containing details the host needs to persist with the transfer in order to be able to react to transfer events like condition fulfillment later.

Ledger plugins MAY attach the `noteToSelf` to the transfer and let the ledger store it. Otherwise it MAY use the [`store`](#TODO) in order to persist this field. Regardless of the implementation, the ledger plugin MUST ensure that all instances of the transfer carry the same `noteToSelf`, even across different machines.

Ledger plugins MUST ensure that the data in the `noteToSelf` either isn't shared with any untrusted party or encrypted before it is shared.

#### executionCondition
<code>**executionCondition**:String</code>

A [cryptographic condition](../0002-crypto-conditions/) used for implementing holds. The underlying ledger MUST hold the transfer until the condition has been fulfilled or the `expiresAt` time has been reached.

Ledger plugins that do not support holds MUST throw an `HoldsNotSupportedError` if this parameter is provided.

Ledger plugins that do support holds, but do not support the given condition type or bitmask MUST throw a  `ExecutionConditionNotSupportedError`.

#### cancellationCondition
<code>**cancellationCondition**:String</code>

A [cryptographic condition](../0002-crypto-conditions/) used for implementing holds. If this condition is met and the transfer is on hold, the ledger MUST cancel the transfer and return the funds to the sender.

Ledger plugins that do not support holds or do not support cancellation MUST throw a `CancellationNotSupportedError` if this parameter is provided.

Ledger plugins that do support cancellation, but do not support the given condition type or bitmask MUST throw a `CancellationConditionNotSupportedError`.

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
  account: 'bob',
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
| `String` | [scale](#scale) | UUID used as an external identifier |
| `String` | [precision](#precision) | UUID used as an external identifier |
| `String` | [currencyCode](#currencyCode) | ISO three-letter currency code |
| `String` | [currencySymbol](#currencySymbol) | UTF8 currency symbol |

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

Plugin options are passed in to the [`LedgerPlugin`](#class-ledgerplugin) constructor when a plugin is being instantiated.

###### Fields
| Type | Name | Description |
|:--|:--|:--|
| `Object` | [auth](#auth) | Ledger authentication information |
| `Object` | [store](#store) | Persistence layer callbacks |

### Fields

#### auth
<code>**auth**:Object</code>

A JSON object that encapsulates authentication information and ledger properties. The format of this object is specific to each ledger plugin.

###### Example
```js
{
  "account": "https://red.ilpdemo.org/ledger/accounts/alice",
  "password": "alice"
}
```

#### store
<code>**store**:Object</code>

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
