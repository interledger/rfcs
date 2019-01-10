---
title: Web Monetization
draft: 5
---

# Web Monetization

Web Monetization is a proposed user's agent API that uses ILP micropayments to monetize a site. It can be provided through a polyfill or an extension, but the goal is to eventually implement it directly into the user's agent.

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

With advertisements, the user's agent decides whether to display the ads and the user decides whether to engage with the ads. With Web Monetization, the user's agent decides whether to pay the site and, if so, how much to pay.

Web Monetization makes use of [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) on top of [ILP/STREAM](../0029-stream/0029-stream.md) to provide a high-level way to send money and data, while still providing tremendous flexibility.

## Flow

This flow refers to the user's agent: in implementation this may be done by an extension a Web Monetization polyfill, or a browser.

- The user visits a webpage.
- The user's agent sets `document.monetizationState` to `pending`.
- The user's agent looks for the Web Monetization `<meta>` tags ([specified below](#meta-tags)). The `<meta>` tags MUST be present once `document.readyState` is `interactive`. Implementations MUST NOT process the tags earlier than this, but MAY wait longer before processing.
  - The `<meta>` tags MUST be in the `<head>` of the document.
  - If the Web Monetization `<meta>` tags are malformed, the user's agent will stop here. The user's agent SHOULD report a warning via the console.
  - If the Web Monetization `<meta>` tags are well-formed, the user's agent should extract the Payment Pointer.
  - The user's agent will generate a fresh UUID (version 4) and use this as the Correlation ID from this point forward. **This Correlation ID MUST be unique per page load**, not per browser, session nor site.
- The user's agent resolves the payment pointer and begins to pay. The payment process MAY be carried out from a different machine acting as the user's agent. Cookies and session information MUST not be carried with any requests made to resolve the Payment Pointer, with the exception of the Correlation ID.
  - On the SPSP query to resolve the Payment Pointer, a `Web-Monetization-Id` header is sent, containing the Correlation ID. The server may use this to associate future requests by the user with their payments.
  - With the `destinationAccount` and `sharedSecret` fetched from the SPSP query, a STREAM connection is established. A single STREAM is opened on this connection, and a positive SendMax is set.
  - The user's agent SHOULD set their SendMax high enough that it is never reached, and make payment adjustments by limiting throughput.
- Once the STREAM connection has fulfilled an ILP packet with a non-zero amount, the user's agent dispatches a `CustomEvent` on `document`. Payment SHOULD continue.
  - The user's agent sets `document.monetizationState` to `started`. This MUST occur before the `monetizationstart` event is fired.
  - The `CustomEvent`'s type is `monetizationstart`. The `CustomEvent`'s `detail` is an object containing the Payment Pointer and the Correlation ID ([specified below](#monetizationstart)).
  - The user's agent also emits a `monetizationprogress` ([specified below](#monetizationprogress)), corresponding to this first packet. If there are no listeners the event MAY NOT be emitted.
- Payment continues until the user closes/leaves the page.
  - The user's agent MAY decide to stop/start payment, e.g. if the user is idle, backgrounds the page, or instructs the browser to do so.
  - If the STREAM connection is severed, it will redo the SPSP query to the same Payment Pointer as before with the same Correlation ID. The user's agent MUST NOT re-process the `<meta>` tags.
  - Each time a packet with a nonzero amount is fulfilled, the user's agent emits a `CustomEvent` on `document`. The `CustomEvent`'s type is `monetizationprogress`. The `CustomEvent`'s `detail` is an object containing the details of the packet ([specified below](#monetizationprogress)). If there are no listeners the event MAY NOT be emitted.

## Specification

### Meta Tags

This `<meta>` tags MUST be in the document's `<head>`. The `<meta>` tags allows the user's agent to pay a site via Web Monetization by specifying a [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md).

If the `<meta>` tag exists inside of an iframe, the iframe MUST have `data-allowmonetization` as an attribute.

The `name` of the `<meta>` tags all start with `monetization:`. The table below lists the different `name`s and the formats of their `content`. Currently there is only one tag, but this may be expanded in the future.

| Name | Required? | Format | Description |
|:--|:--|:--|:--|
| `monetization:paymentpointer` | Yes | [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md) | The Payment Pointer that the user's agent will pay. |

#### Examples

##### Web Monetization Meta Tag

```html
<meta
  name="monetization:paymentpointer"
  content="$twitter.xrptipbot.com/Interledger" />
```

##### Iframe to Web-Monetized Page

```html
<iframe
  src="https://webmonetizedsite.example"
  title="web monetized side"
  data-allowmonetization >
</iframe>
```

### Javascript API

```ts
document.monetizationState: String
```

This can be one of two values.

- `pending` - Indicates that monetization has not yet started. This is set even if there are no Web Monetization `<meta>` tags on the page.
- `started` - Indicates that monetization has started (i.e. the `monetizationstart` event has been fired).

### Browser Events

These events are dispatched on `document`. All Web Monetization events are [`CustomEvent`](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent)s.

#### `monetizationstart`

Dispatched once the first ILP packet with a non-zero amount has been fulfilled by the page's SPSP receiver. MUST be dispatched at least once if payment occurs.

```ts
{
  detail: {
    paymentPointer: String,
    correlationId: String
  }
}
```

The `paymentPointer` matches the one in the `<meta>` tags. The `correlationId` matches the UUID generated by the user's agent (see [Flow](#flow)). This `correlationId` MUST be unique per page load.

#### `monetizationprogress`

Dispatched every time an ILP packet with a non-zero amount has been fulfilled by the page's SPSP receiver (including the first time, when `monetizationstart` is also dispatched). This event MAY NOT be emitted if there are no listeners for it on `document`.

```ts
{
  detail: {
    amount: String,
    assetCode: String,
    assetScale: Number
  }
}
```

- `amount` is a String containing the amount contained in the ILP packet.
- `assetCode` contains the three letter asset code describing the amount's units.
- `assetScale` contains a number representing the scale of the amount. For example, cents would have an assetScale of `2`.

### HTTP Headers

#### `Web-Monetization-Id`

Contains the `correlationId` that the user's agent generated. This header MUST always be sent on SPSP queries for Web Monetization. This value MUST be a UUID version 4.

```http
Web-Monetization-Id: dcd479ad-7d8d-4210-956a-13c14b8c67eb
```
