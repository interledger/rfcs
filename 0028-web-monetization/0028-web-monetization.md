---
title: Web Monetization
draft: 4
---

# Web Monetization

Web Monetization is a proposed browser API that uses ILP micropayments to monetize a site. It can be provided through a polyfill or an extension, but the goal is to eventually implement it directly into the browser.

## Overview

### Terminology

- The **webmaster** is the party who is running a site.
- The **user** is the party who is accessing the site.
- The **provider** is the party providing Interledger access to the user.

### Design Goals

- Should work on mobile and desktop without requiring an extension or special browser.
- Should be extremely simple for webmasters to use in their site.
- Backend infrastructure should be optional; should be usable on a static site.
- Should not require any interaction with the user.
- Should give user's agent a choice about how much to spend, and which sites to support.
- Should give advanced webmasters a way to associate payments with their users, in order to unlock premium experiences.
- Should pay continuously as the user consumes content.
- Should be compatible with existing application and transport protocols on Interledger.

### Relation to Other Protocols

The reason this is not using the W3C Web Payments API is that Web Monetization is intended for continuous payments rather than discrete payments. It is also not designed to have any user interaction. The idea is to provide a direct alternative to advertisements, rather than an alternative to existing checkout methods.

With advertisements, the browser decides whether to display the ads and the user decides whether to engage with the ads. With Web Monetization, the browser decides whether to pay the site and, if so, how much to pay.

Web Monetization makes use of [ILP/STREAM](../0029-stream/0029-stream.md) provide a high-level way to send money and data, while still providing tremendous flexibility.

## Flow

Web Monetization works in two stages: first, the user registers their provider with their browser. After the registration has been completed, the user can go to websites and use Web Monetization.

### Registration

- The user visits their provider's webpage.
- The provider's webpage calls `window.WebMonetization.register`.
- The browser will display a native pop-up box asking the user whether they want to set the handler proposed by the page.
  - If the user confirms, `handlerUrl` is stored in the browser's state and `window.WebMonetization.register` resolves to true.
  - If the user cancels the registration, `window.WebMonetization.register` will resolve to false.

### Monetization

- The user visits a webpage.
- When the page wants to open an ILP/STREAM connection, it calls `window.WebMonetization.monetize()` with a `destinationAccount` and `sharedSecret`.
  - The browser creates an iframe to the handler URL, reading from the state that was stored during [registration](#registration).
  - An ILP/STREAM connection object is returned from the function for the site to use.
- When the page wants to use the ILP/STREAM connection, they use the javascript STREAM API to send money and/or data. The browser sends outgoing ILP packets to the handler iframe using `postMessage`. The handler iframe forwards incoming packets by calling `window.parent.postMessage`.

## Specification

### Browser API / Polyfill API

#### Register

```ts
window.WebMonetization.register({
  name: string,
  handlerUri: string
}): Promise<Boolean>
```

##### Parameters

| Name | Type | Description |
|:---|:---|:---|
| opts | `Object` | The options for registering a handler. |
| opts.name | `String` | Name of the provider (for display). |
| opts.handlerUri | `String` | URL to handler. |

##### Returns

- `Promise<Boolean>` - Whether the handler was set successfully.

#### Monetize

```ts
window.WebMonetization.monetize({
  destinationAccount: string,
  sharedSecret: string
}): Promise<IlpConnection>
```

##### Parameters

| Name | Type | Description |
|:---|:---|:---|
| opts | `Object` | The options for creating a connection. |
| opts.destinationAccount | `String` | ILP address for STREAM server. |
| opts.sharedSecret | `String` | Base64 representation of STREAM shared secret. |

##### Returns

- `Promise<IlpConnection>` - An [ILP/STREAM connection](#ilp-connection-class) that can be used to send money and data.
- Rejects with `Error` if the connection could not be established.
- Rejects with `NoHandlerRegisteredError` if the browser is not enabled for Web Monetization and/or has no handler registered.

### ILP Connection Class

#### Events

| Name | Fields | Emitted |
|:---|:---|:---|
| `stream` | [`Event.stream: IlpStream`](#ilp-stream-class) | When the other side of the connection opens a stream. |
| `close` | | When the connection closes. |
| `error` | `Event.error: Error` | When an error occurs on this ILP connection. |

#### Fields (Read-only)

| Name | Type | Description |
|:---|:---|:---|
| `connectionTag` | `String` | A unique tag on this connection set at establishment. |
| `lastPacketExchangeRate` | `Number` | Exchange rate observed on the most recent packet over this connection. |
| `minimumAcceptableExchangeRate` | `Number` | The least favorable connection allowed on this exchange rate. |
| `totalDelivered` | `String` | The amount of money sent to the destination (in destination units). |
| `totalSent` | `String` | The amount of money sent to the destination (in our units). |
| `totalReceived` | `String` | The amount of money received (in our units). |
| `sourceAssetCode` | `String` | The three-letter asset code of the source account's units. |
| `sourceAssetScale` | `Number` | The scale of the source account's units (i.e. if the units were cents, the scale would be `2` and the code would be `USD`) |
| `destinationAssetCode` | `String | undefined` | The three-letter asset code of the destination account's units. This may not be present, depending on the destination's STREAM version. |
| `destinationAssetScale` | `String | undefined` | The scale of the destination account's units. This may not be present, depending on the destination's STREAM version. |

#### Create Stream

```ts
connection.createStream(): IlpStream
```

##### Returns

- `IlpStream` - An [ILP Stream](#ilp-stream-class) object.

#### End Connection

```ts
connection.close(): void
```

### ILP Stream Class

#### Events

| Name | Fields | Emitted |
|:---|:---|:---|
| `data` | `Event.data: Uint8Array` | When data is received over the stream. |
| `money` | `Event.amount: String` | When money is received over the stream. |
| `outgoing_money` | `Event.amount: String` | When money is sent over the stream. |
| `close` | | When the stream is closed. |
| `error` | `Event.error: Error` | When the stream encounters an error. |

#### Fields (Read-only)

| Name | Type | Value |
|:---|:---|:---|
| `id` | `String` | The id of this stream, unique to this connection. |
| `receiveMax` | `String` | The maximum amount you permit this stream to receive. Change with `setReceiveMax()` |
| `sendMax` | `String` | The amount you will try to send on this stream. Change with `setSendMax()` |
| `totalReceived` | `String` | The total amount received so far on this stream. |
| `totalSent` | `String` | The total amount sent so far on this stream. |

#### Check if Stream is Open

```ts
stream.isOpen(): Boolean
```

##### Returns

- `Boolean`, whether the stream is open.

#### Allow Money to be Received

```ts
stream.setReceiveMax(amount: String): void
```

Sets the maximum that can be received. Must be called with
increasing values.

##### Parameters

- `amount: String` - The amount to receive (in our units).

#### Wait for Money to be Received

```ts
stream.receiveTotal(amount: String, timeout?: Number): Promise<void>
```

Sets the maximum that can be received and waits until that amount has been
reached. Must be called with increasing `amount`s.

##### Parameters

- `amount: String` - The amount to receive (in our units).
- `timeout: Number` - How long (in ms) to wait for this function to complete.

#### Try to Send Money

```ts
stream.setSendMax(amount: String): Promise<void>
```

Sets the maximum that can be sent. The stream will send as much as the receiver
is willing to receive, up to this maximum.The stream will send as much as the
receiver is willing to receive, up to this maximum. Must be called with
increasing values.

##### Parameters

- `amount: String` - The amount to send (in our units).

#### Wait for Money to be Sent

```ts
stream.sendTotal(amount: String, timeout?: Number): Promise<void>
```

Sets the maximum that can be sent and waits until that amount has been
sent. Must be called with increasing `amount`s.

##### Parameters

- `amount: String` - The amount to send (in our units).
- `timeout: Number` - How long (in ms) to wait for this function to complete.

#### Send Data on the Stream

```ts
stream.send(msg: Uint8Array | String): Promise<void>
```

Sends data over the stream, which will be emitted as `data` events on the other
side. The data may be broken into chunks or buffered; one `send` call doesn't
necessarily correspond to a single `data` event.

##### Parameters

- `msg: Uint8Array | String` - The data to send over the stream.

#### Close the Stream

```ts
stream.close(): void
```

### Web Monetization Handler API

The `handlerURL` that is registered is embedded as an iframe. Messages are passed to it with `iframe.contentWindow.postMessage`, and messages are sent from the iframe to the browser via `window.parent.postMessage`.

#### Request

```ts
{
  id: string,
  request: string
}
```

| Name | Type | Description |
|:---|:---|:---|
| id | `String` | Unique ID to associate request with response. |
| request | `String` | Base64 encoded ILP prepare packet. |

#### Response (Success)

```ts
{
  id: string,
  response: string
}
```

| Name | Type | Description |
|:---|:---|:---|
| id | `String` | Unique ID to associate request with response. |
| response | `String` | Base64 encoded ILP fulfill/reject packet. |

#### Response (Error)

```ts
{
  id: string,
  error: string,
  errorName?: string
}
```

| Name | Type | Description |
|:---|:---|:---|
| id | `String` | Unique ID to associate request with response. |
| error | `String` | Error message. |
| errorName | `String` | _(Optional)_ Error name. |
