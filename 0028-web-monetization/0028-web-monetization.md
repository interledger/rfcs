---
title: Web Monetization
draft: 5
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

Web Monetization makes use of [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) on top of [ILP/STREAM](../0029-stream/0029-stream.md) to provide a high-level way to send money and data, while still providing tremendous flexibility.

## Flow

This flow refers to the user's browser, but in implementation this may actually be done by an extension or a Web Monetization polyfill.

- The user visits a webpage.
- The user's browser looks for the Web Monetization `<meta>` tag ([specified below](#meta-tag)). The `<meta>` tag MUST be present once `document.readyState` is `interactive`. Implementations MUST NOT look process the tag earlier than this, but MAY wait longer before processing.
  - The `<meta>` tag MUST be in the `<head>` of the document.
  - If the Web Monetization `<meta>` tag is malformed, the browser will stop here. The browser SHOULD report a warning via the console.
  - If the Web Monetization `<meta>` tag is well-formed, the browser should extract the Payment Pointer and Correlation ID.
  - If no Correlation ID is present on the `<meta>` tag, the browser will generate a fresh UUID (version 4) and use this as the Correlation ID from this point forward.
- The user's browser dispatches a [`CustomEvent`](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent) on `window`, indicating that the Web Monetization tag has been recognized and payment will be made.
  - The `CustomEvent`'s type is `webmonetizationload`. The `CustomEvent`'s `detail` is an object containing the Payment Pointer and the Correlation ID ([specified below](#webmonetizationload))
- The user's browser resolves the payment pointer and begins to pay. The payment process MAY be carried out from a different machine acting as the user's agent. Cookies and browser headers MAY not be carried with any requests made to resolve the Payment Pointer.
  - On the SPSP query to resolve the Payment Pointer, a `Web-Monetization-Id` header is sent, containing the Correlation ID. The server may use this to associate future requests by the user with their payments.
  - With the details fetched from the SPSP query, a STREAM connection is established. A single STREAM is opened on this connection, and a positive SendMax is set.
  - The browser SHOULD set their SendMax high enough that it is never reached, and make payment adjustments by limiting throughput.
- Once the STREAM connection has fulfilled an ILP packet with a non-zero amount, the user's browser dispatches a `CustomEvent` on `window`. Payment SHOULD continue.
  - The `CustomEvent`'s type is `webmonetizationstart`. The `CustomEvent`'s `detail` is an object containing the Payment Pointer and the Correlation ID ([specified below](#webmonetizationstart)).
- Payment continues until the user closes/leaves the page.
  - The browser MAY decide to stop/start payment, e.g. if the user is idle, backgrounds the page, or instructs the browser to do so.
  - If the browser's STREAM connection is severed, it will redo the SPSP query to the same Payment Pointer as before with the same Correlation ID. The browser MUST NOT re-process the `<meta>` tag.

## Specification

### Meta Tag

This `<meta>` tag MUST be in the document's `<head>`. The `<meta>` tag allows the browser to pay a site via Web Monetization by specifying a [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md). It may also specify a Correlation ID which will be included during SPSP queries under the `Web-Monetization-Id` header.

The `name` of the meta tag MUST be `webmonetization`.

The `content` of the meta tag is a query string. It MUST NOT exceed 1000 characters. The possible entries are listed below:

| Name | Required? | Format | Description |
|:--|:--|:--|:--|
| `paymentPointer` | Yes | [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md) | The Payment Pointer that the browser will pay. |
| `correlationId` | No | [base64url](https://tools.ietf.org/html/rfc4648#section-5) | An ID to associate payment with the browser. |

#### Examples

##### Without Correlation ID

```html
<meta
  name="webmonetization"
  content="paymentPointer=$twitter.xrptipbot.com/Interledger" />
```

##### With Correlation ID

```html
<meta
  name="webmonetization"
  content="paymentPointer=$twitter.xrptipbot.com/Interledger&correlationId=dcd479ad-7d8d-4210-956a-13c14b8c67eb"
/>
```

### Browser Events

These events are dispatched on `window`. All Web Monetization events are [`CustomEvent`](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent)s.

#### `webmonetizationload`

Dispatched when web monetization has successfully processed the [Web
Monetization `<meta>` tag](#meta-tag). MUST NOT be dispatched after `webmonetizationstart`.

```ts
{
  detail: {
    paymentPointer: String,
    correlationId: String
  }
}
```

The `paymentPointer` matches the one in the `<meta>` tag. The correlationId matches the one in the `<meta>` tag if specified, and is otherwise generated as a random UUID (see [Flow](#flow)).

#### `webmonetizationstart`

Dispatched once the first ILP packet with a non-zero amount has been fulfilled by the page's SPSP receiver. MUST be dispatched after `webmonetizationload`. MUST be dispatched at least once.

```ts
{
  detail: {
    paymentPointer: String,
    correlationId: String
  }
}
```

The `paymentPointer` and `correlationId` are both the same as when `webmonetizationload` was dispatched.

### HTTP Headers

#### `Web-Monetization-Id`

Contains the `correlationId` that the browser got from the `<meta>` tag or generated itself. This header MUST always be sent on SPSP queries for Web Monetization.

The value is restricted to the [base64url](https://tools.ietf.org/html/rfc4648#section-5) set of characters. It MUST NOT exceed 1000 characters.

```http
Web-Monetization-Id: dcd479ad-7d8d-4210-956a-13c14b8c67eb
```
