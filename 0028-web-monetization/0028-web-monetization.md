---
title: Web Monetization
draft: 9
---

# Web Monetization

Web Monetization is a proposed browser API that uses ILP micropayments to monetize a site. It can be provided through a polyfill or an extension, but the goal is to eventually implement it directly into the user's browser.

## Overview

### Terminology

- The **user** is the party who is accessing the web-monetized site.
- The **provider** is the party providing Interledger access to the user.
- The **browser** is the web browser used by the user, which may include extensions that implement Web Monetization.

### Design Goals

- Should be extremely simple for webmasters to use in their site.
- Backend infrastructure should be optional; should be usable on a static site.
- Should not require any interaction with the user.
- Should give user's browser a choice about how much to spend, and which sites to support.
- Should give advanced webmasters a way to associate payments with their users, in order to unlock premium experiences.
- Should pay continuously as the user consumes content.
- Should be compatible with existing application and transport protocols on Interledger.

### Relation to Other Protocols

The W3C have published two payments related APIs for browsers, the Payment Request API and the Payment Handler API.

The reason this API is not using the Payment Request API directly is that Web Monetization is intended for continuous payments rather than discrete payments. It is also not designed to have any user interaction. It is intended to provide a direct alternative to advertisements, rather than an alternative to existing checkout methods.

Some changes will be required to Payment Request and Payment Handler to fully support Web Monetization in future, however this API brings the necessary features to the browser in a way that allows for tighter integration in the future.

With advertisements, the user's browser decides whether to display the ads and the user decides whether to engage with the ads. With Web Monetization, the user's provider decides whether to pay the site and, if so, how much to pay.

Web Monetization makes use of [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) on top of [ILP/STREAM](../0029-stream/0029-stream.md) to provide a high-level way to send money and data, while still providing tremendous flexibility.

## Flow

This flow refers to the user's **browser** and the user's **provider**, [defined above](#terminology).

- The user's browser navigates to a webpage.
- The user's browser sets `document.monetization` to an Object which implements [EventTarget](https://developer.mozilla.org/en-US/docs/Web/API/EventTarget).
- The user's browser sets `document.monetization.state` to `pending`.
- The user's browser observes the `<head>` and looks for a Web Monetization `<meta name="monetization">` tag ([specified below](#meta-tags-set)).
  - There MUST be only one `<meta name="monetization">` tag at any given time
  - The `<meta>` Tags Set MUST be in the `<head>` of the document.
  - The `<meta>` Tags Set MUST be in the top level window (i.e. not inside an iframe)

- Below is repeated for every semantically (consider `meta.content = meta.content`) new  `<meta name="monetization">` tag seen for the life of the page:
  - If any of the Web Monetization `<meta>` Tags Set are malformed, the browser will stop here. The user's browser SHOULD report a warning via the console.
  - If the Web Monetization `<meta name="monetization">` tag is well-formed, the browser should extract the Payment Setup Endpoint ([Payment Pointer](../0026-payment-pointers) or [SPSP](../0009-simple-payment-setup-protocol) Url).
  - The user's browser generates a fresh **random** UUID (version 4) and uses this as a Monetization ID. This MUST be regenerated upon dynamic changes to the meta tags and MUST be unique per page load in order to avoid user tracking.
  - The user's browser passes these payment details to the user's provider (see [Payment Handler Flow](#payment-handler-flow)).
  - The provider resolves the Payment Setup Endpoint and begins to pay. The provider MAY be acting from a different machine from the user. Cookies and session information MUST NOT be carried with any requests made to resolve the Payment Setup Endpoint, with the exception of the Monetization ID.
    - On the SPSP query to resolve the Payment Setup Endpoint, a `Web-Monetization-Id` header is sent, containing the Monetization ID. The server running the web-monetized site may use this to associate future requests by the user with their payments.
    - With the `destination_account` and `shared_secret` fetched from the SPSP query, a STREAM connection is established. A single STREAM is opened on this connection, and a positive SendMax is set.
    - The provider SHOULD set their SendMax high enough that it is never reached, and make payment adjustments by limiting throughput.
  - Once the STREAM connection has fulfilled an ILP packet with a non-zero amount, the provider notifies the browser:
    - The user's browser sets `document.monetization.state` to `started`.
    - This MUST occur before the `monetizationstart` event is fired.
    - This event has a `detail` field with an object containing the Payment Setup Endpoint and the Monetization ID ([specified below](#monetizationstart)).
    - The user's browser also emits a `monetizationprogress` ([specified below](#monetizationprogress)) event from `document.monetization`, corresponding to this first packet. If there are no listeners the event MAY NOT be emitted.
  - Payment continues for the lifetime of a given meta tag (or semantically equivalent)
    - The provider MAY decide to stop/start payment at any time, e.g. if the user is idle, backgrounds the page, or instructs the browser to do so.
    - If the STREAM connection is severed, the provider will redo the SPSP query to the same Payment Setup Endpoint as before with the same Monetization ID. The user's browser MUST NOT re-process the `<meta>` Tags Set.
    - Each time a packet with a nonzero amount is fulfilled, the provider notifies the browser, and the browser emits an event on `document.monetization`. The event's type is `monetizationprogress`. The event has a `detail` field containing the details of the packet ([specified below](#monetizationprogress)). If there are no listeners the event MAY NOT be emitted.
    - When a stream is closed the `document.monetization.state` MUST be set back to 'pending'

### Payment Handler Flow

A provider can be implemented as a Payment Handler supporting the 'webmonetization' payment method (The payment method specification for this payment method is still under development.). Communication between the browser and the provider would use this flow.

- After parsing the `<meta>` Tags Set, the browser creates a new [PaymentRequest](https://www.w3.org/TR/payment-request/#paymentrequest-interface) object with the following [PaymentMethodData](https://www.w3.org/TR/payment-request/#dom-paymentmethoddata) argument.

```json
{
  "supportedMethods": "webmonetization",
  "data": {
    "paymentPointer": "{{ payment pointer parsed from meta tag }}"
  }
}
```

- The user's browser calls `.show()` on this PaymentRequest, triggering the [PaymentHandler](https://www.w3.org/TR/payment-handler/) for `webmonetization`. This PaymentHandler is how the browser communicates to the provider.
  - The return value of `.show()` MUST return a Promise, and must also implement the [EventTarget](https://developer.mozilla.org/en-US/docs/Web/API/EventTarget) interface. The provider will emit [MonetizationStart](#monetizationstart) and [MonetizationProgress](#monetizationprogress) events from this Promise to communicate to the browser when payment occurs. The Promise MUST NOT resolve, because Web Monetization continues for the entire lifetime of a given meta tag. The Promise MAY reject if there is an error preventing the provider from paying and no retries will occur.
  - This PaymentHandler MUST NOT require any UI or confirmation to proceed with payment.

## Specification

### Meta Tags Set

The `<meta>` Tags Set MUST be in the document's `<head>`. The `<meta>` Tags Set allows the user's browser to pay a site via Web Monetization by specifying a [Payment Pointer](../0026-payment-pointers/0026-payment-pointers.md) or [SPSP](../0009-simple-payment-setup-protocol) url.

The `name` of the `<meta>` tags all start with `monetization`. The table below lists the different `name`s and the formats of their `content`. Currently there is only one tag, but this may be expanded in the future so care MUST be given to altering a Tags Set such that `<meta name="monetization">` is the last one modified.   


| Name | Required? | Format | Description |
|:--|:--|:--|:--|
| `monetization` | Yes | Payment Setup Endpoint | The [Payment Pointer]((../0026-payment-pointers/0026-payment-pointers.md)) or SPSP url that the user's browser will pay to. |

#### Examples

##### Web Monetization Meta Tag

```html
<meta
  name="monetization"
  content="$twitter.xrptipbot.com/Interledger">
```

### Javascript API

```ts
document.monetization: EventTarget
document.monetization.state: string
```

`document.monetization.state` can be one of two values.

- `pending` - Indicates that monetization has not yet started. This is set even if there are no Web Monetization `<meta>` tags on the page.
- `started` - Indicates that monetization has started (i.e. the `monetizationstart` event has been fired).

### Browser Events

These events are dispatched on `document.monetization`. Web Monetization events MAY be implemented as [`CustomEvent`](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent)s, or as their own Event class.

#### `monetizationstart`

Dispatched once the first ILP packet with a non-zero amount has been fulfilled by the page's SPSP receiver. MUST be dispatched at least once if payment occurs.

```ts
{
  detail: {
    // Payment Setup Endpoint
    paymentPointer: string,
    // Monetization ID / Web-Monetization-Id header
    requestId: string
  }
}
```

The `paymentPointer` matches the one in the `<meta name="monetization">` tag. The `requestId` matches the Monetization ID (UUID V4) generated by the browser (see [Flow](#flow)).

#### `monetizationprogress`

Dispatched every time an ILP packet with a non-zero amount has been fulfilled by the page's SPSP receiver (including the first time, when `monetizationstart` is also dispatched). This event MAY NOT be emitted if there are no listeners for it on `document.monetization`.

```ts
{
  detail: {
    // Received amount
    amount: string,
    assetCode: string,
    assetScale: number
  }
}
```

- `amount` is a String containing the destination amount **received** as specified in the ILP packet.
- `assetCode` contains the three letter asset code describing the amount's units.
- `assetScale` contains a number representing the scale of the amount. For example, cents would have an assetScale of `2`.

### HTTP Headers

#### `Web-Monetization-Id`

Contains the `Monetization ID` (currently referred to as `requestId` in the events) that the browser generated. This header MUST always be sent on SPSP queries for Web Monetization. This value MUST be a UUID version 4.

```http
Web-Monetization-Id: dcd479ad-7d8d-4210-956a-13c14b8c67eb
```
