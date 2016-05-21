# Ledger Plugin Interface

The Interledger Protocol is a protocol suite for connecting blockchains and other ledgers.

This spec defines a ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP spec](../0003-interledger-protocol/).



## Static Methods

### Plugin.canConnectToLedger(auth)

Returns `Boolean`


## Ledger Management

### p = new Plugin(opts)

`opts`:
```js
{
  auth: {
    // auth parameters are defined by the plugin
  },
  store: {
    // persistence may be required for internal use by some ledger plugins
    // (e.g. when the ledger has reduced memo capability and we can only put an ID in the memo)
    get: function (key) {
      // Returns Promise.<Object|Error>
    },
    set: function (key, value) {
      // Returns Promise.<Object|Error>
    },
    remove: function (key) {
      // Returns Promise.<Object|Error>
    }
  }
}
```

### p.isConnected()

Returns `Boolean`

### p.getPrecision()

Returns `Promise.<Object|Error>`

```json
{
  "precision": 10,
  "scale": 4
}
```

### p.getConnectors()

Return an array of opaque local destination identifiers representing neighboring connectors.

Returns `Promise.<Array<String>|Error>`

### p.connect()

Returns `Promise.<null|Error>`

### p.disconnect()

Returns `Promise.<null|Error>`

### p.on('connect', function () {})

Returns `p` (for chaining)

### p.on('disconnect', function () {})

Returns `p` (for chaining)

### p.on('connect_error', function () {})

Returns `p` (for chaining)

### p.on('reconnect', function () {})

Returns `p` (for chaining)

### p.on('error', function () {})

Returns `p` (for chaining)

## Ledger Transfers

Note that all transfers will have `transferId`'s to allow the plugin user to correlate actions related to a single transfer. The `transferId` will be the same as the ID used by the underlying ledger wherever possible or applicable. If the ledger does not have transfer IDs, the plugin may generate one and use the `store` passed in to the constructor to persist them.

### p.send(localParams, ilpPacket)

Initiates a local transfer. A transfer can contain money and/or information.

Some ledger plugins MAY implement zero-amount transfers differently than other transfers.

`localParams`:

```js
{
  uniqueToken: 'd86b0299-e2fa-4713-833a-96a6a75271b8',
  localDestination: 'https://ledger.example/accounts/connector',
  amount: '10',
  noteToSelf: {},

  // for UTP/ATP support
  executionCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0',

  // for UTP support
  expiresAt: '2016-05-18T12:00:00.000Z',

  // for ATP support
  cancellationCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0'
}
```

##### localParams.uniqueToken

A unique identifier. The ledger plugin MUST NOT take any action if a transfer with this token already exists.

##### localParams.localDestination

A local destination identifier. The identifier is a string. The format is defined by each ledger plugin and is opaque.

##### localParams.amount

A decimal amount, represented as a string. MUST be positive. The supported precision is defined by each ledger plugin. The ledger plugin MUST throw an error if the given amount exceeds the supported level of precision.

##### localParams.noteToSelf

An optional object containing details the plugin user needs to persist with the transfer to be able to correlate the transfer later with another transfer or action outside of this ledger.

Note that if the ledger supports attaching memos for the sender as well as receiver of a transfer, this will modify the transfer and add the `noteToSelf` as such a memo. Otherwise, it will be persisted locally using the `store`.

##### localParams.executionCondition

A cryptographic condition used for implementing holds. The underlying ledger should hold the transfer until the condition has been fulfilled or the `expiresAt` time has been reached.

Ledger plugins that do not support holds MUST throw an error if this parameter is provided.

##### localParams.expiresAt

A timestamp representing the expiry date for the transfer.

Ledger plugins that do not support holds MUST throw an error if this parameter is provided.

##### localParams.cancellationCondition

A crpytographic condition used for implementing holds. If this condition is met and the transfer is on hold, the transfer should be canceled and the funds should be returned to the sender.

Ledger plugins that do not support cancellation MUST throw an error if this parameter is provided.

Ledger plugins MAY accept additional parameters for other features they support.

##### ilpPacket

A buffer containing the ILP packet ((TODO LINK)). Besides the ILP header, this packet MAY include a transport layer header, a quote request or other message.

Returns the transfer ID (`Promise.<String>`).

### p.fulfillTransferCondition(transferId, fulfillment)

Returns `Promise.<null>`

### p.replyToTransfer(transferId, replyMessage)

**TODO**: Define what the message format is

Returns `Promise.<null>`

### p.on('incoming', function ({ transfer, ilpPacket }) {})

The ledger plugin MUST authenticate the source for all incoming transfers, whether they include money or not.

`transfer`:

```js
{
  id: 'https//ledger.example/transfers/123',
  localSource: 'https://ledger.example/accounts/connector',
  amount: '10',
  noteToSelf: {},

  // for UTP/ATP support
  executionCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0',

  // for UTP support
  expiresAt: '2016-05-18T12:00:00.000Z',

  // for ATP support
  cancellationCondition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0'
}
```

Returns `p` (for chaining)

### p.on('condition_fulfill', function ({ transfer, ilpPacket, fulfillment }) {})

Returns `p` (for chaining)

### p.on('reject', function ({ transfer, ilpPacket, rejectionReason }) {})

The `rejectionReason` is a ledger plugin-specific error.

Returns `p` (for chaining)

### p.on('reply', function ({ transfer, ilpPacket, replyMessage }) {})

Returns `p` (for chaining)
