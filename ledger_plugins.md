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
    // persistence may be required for some ledger plugins
    // (e.g. when the ledger has reduced memo capability and we can only put an ID in the memo)
    get: function (key) {},
    set: function (key, value) {},
    remove: function (key) {}
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

#### p.createTransfer(packet, quote)

Returns `Object`

```js
{
  localTransferId: '...', // opaque string
  transfer: {...} // Object|Buffer|String
}
```

TODO: should this be synchronous or async to allow for the possibility of proposing the transfers first? That might be useful for some ledgers

#### p.prepareTransfer(transfer)

Returns `Promise.<String|Error>`

Return value is the `localTransferId`

#### p.executeTransfer(localTransferId, fulfillment)

Returns `Promise.<null|Error>`

#### p.cancelTransfer(localTransferId, cancellationConditionFulfillment)

Returns `Promise.<null|Error>`

Note that not all transfers will be cancellable.

#### p.on('transfer_prepared', function (localTransferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_executed', function (localTransferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_rejected', function (localTransferId, transfer) {})

Returns `p` (for chaining)

#### p.on('transfer_cancelled', function (localTransferId, transfer) {})

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
