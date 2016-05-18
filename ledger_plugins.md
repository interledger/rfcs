# Ledger Plugin Framework (DRAFT)

The Interledger Protocol is a protocol suite for connecting blockchains and other ledgers.

This spec defines a ledger abstraction interface for Interledger clients and connectors to communicate and route payments across different ledger protocols.

To send ILP payments through a new ledger, one must implement a ledger plugin that exposes the interface defined below. This can be used with the ILP Client and Connector and should work out of the box.

This spec depends on the [ILP Packet spec](./ilp_packet.md).

## Ledger Plugin Interface

### Plugin.canConnectToLedger(auth)

Returns `Promise.<Boolean|Error>`

### Plugin.getPacketFromTransfer(transfer)

Returns `ILPPacket`

### Plugin.matchesPacket(transfer, packet)

Returns `Boolean`

Used by the receiver to verify that the incoming transfer actually matches the given packet (checks amounts, condition, expiry and data if applicable)

### Plugin.getExpiryFromTransfer(transfer)

Returns `String`

### p = new Plugin(auth)

Auth fields are defined by ledger plugin

### p.checkHealth()

Returns `Promise.<Boolean|Error>`

TODO: should this return a boolean, null, or an object with information? If it's an object it would need to be standardized. It might be easiest not to return substantive information

### p.getPrecision()

Returns `Promise.<Object|Error>`

```json
{
  "precision": 10,
  "scale": 4
}
```

### p.connect()

Returns `Promise.<null|Error>`

### p.disconnect()

Returns `Promise.<null|Error>`

### p.getConnectors()

Returns `Promise.<Array<String>|Error>`

TODO: should this return an array of strings or objects? It seems like the connector identifiers would just need to be something that would be understood by `sendMessage()`

### p.sendMessage(node, message)

TODO: should we have a generic sendConnectorMessage function or specific functions for getQuote, routeUpdate, etc?

### p.on('message', function (message, source) {})

Returns `null`

TODO: need to verify the source of the messages

### p.createTransfer(packet, quote)

Returns `Object|Buffer|String`

### p.prepareTransfer(transfer)

Returns `Promise.<null|Error>`

### p.executeTransfer(transfer, fulfillment)

Returns `Promise.<null|Error>`

### p.cancelTransfer(transfer, cancellationConditionFulfillment)

Returns `Promise.<null|Error>`

Note that not all transfers will be cancellable.

### p.on('transfer', function (transfer) {})

Returns `Promise.<null|Error>`
