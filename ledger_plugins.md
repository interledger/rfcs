# Ledger Plugin Framework (DRAFT)

The Interledger Protocol is a protocol suite for connecting blockchains and other ledgers.

This spec defines a ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP Packet spec](./ilp_packet.md).

## Ledger Plugin Interface




### Static Methods

#### Plugin.canConnectToLedger(auth)

Returns `Promise.<Boolean|Error>`

#### Plugin.getPacketFromTransfer(transfer)

Returns `Object`

Return value is an ILPPacket in JSON form

#### Plugin.matchesPacket(transfer, packet)

Returns `Boolean`

Used by the receiver to verify that the incoming transfer actually matches the given packet (checks amounts, condition, expiry and data if applicable)

#### Plugin.getExpiryFromTransfer(transfer)

Returns `String`




### Ledger Management

#### p = new Plugin(opts)

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
      // Returns Promsise.<Object|Error>
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

#### p.checkHealth()

Returns `Promise.<Boolean|Error>`

TODO: should this return a boolean, null, or an object with information? If it's an object it would need to be standardized. It might be easiest not to return substantive information

#### p.getPrecision()

Returns `Promise.<Object|Error>`

```json
{
  "precision": 10,
  "scale": 4
}
```

#### p.connect()

Returns `Promise.<null|Error>`

#### p.disconnect()

Returns `Promise.<null|Error>`




### Ledger Transfers

Note that all transfers will have `transferId`'s to allow the plugin user to correlate actions related to a single transfer. The `transferId` will be the same as the ID used by the underlying ledger wherever possible or applicable. If the ledger does not have transfer IDs, the plugin may generate one and use the `store` passed in to the constructor to persist them.

#### p.createTransfer(params)

`params`:

TODO: these fields should be similar to those in the packet format

```js
{
  id: 'd86b0299-e2fa-4713-833a-96a6a75271b8', // one will be generated if it is not provided
  destination: 'https://ledger.example/accounts/connector',
  amount: '10',
  expiresAt: '2016-05-18T12:00:00.000Z',
  condition: 'cc:0:3:47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU:0'
  packet: {
    // ILP Packet to be passed on to the next connector
  },
  // The `noteToSelf` is for plugin users to include details for correlating this transfer with other transfers or actions outside of this ledger
  // When supported by the ledger, this will be included in the transfer
  // Otherwise, it will be persisted locally to the `store`
  noteToSelf: {
    sourceTransferId: 'af35a5a2-a3a0-4e96-bb52-244a429c6613'
  }
}
```

Returns `Promise.<Object|Error>`

```js
{
  transferId: '...', // opaque string
  transfer: {...} // Object|Buffer|String
}
```

#### p.prepareTransfer(transfer)

Returns `Promise.<String|Error>`

Return value is the `transferId`

#### p.executeTransfer(transferId, fulfillment)

Returns `Promise.<null|Error>`

#### p.cancelTransfer(transferId, cancellationConditionFulfillment)

Returns `Promise.<null|Error>`

Note that not all transfers will be cancellable.

#### p.on('transfer_prepared', function (transferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_executed', function (transferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_rejected', function (transferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_cancelled', function (transferId, transfer) {})

Returns `p` (for chaining)

TODO: should cancelled and rejected be the same event? If so, how should you differentiate them?




### Connector Communication

#### p.getConnectors()

Returns `Promise.<Array<String>|Error>`

TODO: should this return an array of strings or objects? It seems like the connector identifiers would just need to be something that would be understood by `sendMessage()`

#### p.sendMessage(node, message)

TODO: should we have a generic sendConnectorMessage function or specific functions for getQuote, routeUpdate, etc?

#### p.on('message', function (message, source) {})

Returns `p` (for chaining)

TODO: need to verify the source of the messages
