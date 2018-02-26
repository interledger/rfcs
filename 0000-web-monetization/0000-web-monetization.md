---
title: Web Monetization
draft: 1
---

# Web Monetization

Web Monetization is a proposed browser API that uses ILP micropayments to monetize a site. It can be polyfilled by extensions, or can be implemented directly into an ILP-enabled browser.

## Overview

### Terminology

- The **webmaster** is the party who is running a site.
- The **user** is the party who is accessing the site.

### Design Goals

- Should be extremely simple for webmasters to use in their site.
- Backend infrastructure should be optional; should be usable on a static site.
- Should not require any interaction with the user.
- Should give user's agent a choice about how much to spend, and which sites to support.
- Should give advanced webmasters a way to associate payments with their users, in order to unlock premium experiences.
- Should pay continuously as the user consumes content.

### Relation to Other Protocols

The reason this is not using the W3C Web Payments API is that Web Monetization is intended for continuous payments rather than discrete payments. It is also not designed to have any user interaction. The idea is to provide a direct alternative to advertisements, rather than an alternative to existing checkout methods.

With advertisements, the browser decides whether to display the ads and the user decides whether to engage with the ads. With Web Monetization, the browser decides whether to pay the site and, if so, how much to pay.

Web Monetization makes use of [Payment Pointers](../0026-payment-pointers/0026-payment-pointers.md) in order to associate a site with an ILP destination, and [SPSP](../0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md) in order to set up ILP payments.

The browser or browser extension which provides Web Monetization will likely use the [Ledger Plugin Interface](../0004-ledger-plugin-interface/0004-ledger-plugin-interface) in order to trigger payment when a site requests it.

## Flow

- The user visits a webpage. The page is loaded and the page's javascript is run.
- The site checks whether `window.monetize` is defined. This function is injected into the page by the browser or browser extension which provides Web Monetization.
- If `window.monetize` is not defined, the webpage may show the user a message asking them to install a Web Monetization extension in order to support this site.
- If `window.monetize` is defined, the webpage calls `monetize({ receiver })`, where `receiver` is their payment pointer. This function returns a promise.
- The user's browser or Web Monetization extension decides whether to pay the page.
- If the user's browser decides not to pay, an error is thrown from the `monetize` promise.
- If the user's browser pays, the `monetize` promise resolves.
- The webpage may run some code in order to thank the user or offer them additional content. This does not guarantee that the site way paid, because it runs client-side. If confirmation of receipt is required, the backend which provides the SPSP server can be queried.

## Specification

#### monetize

`window.monetize({ receiver: string }) -> Promise<void>`

Request the user's browser or Web Monetization extension to send money to the specified `receiver`.
If the browser does not support Web Monetization and there is no Web Monetization extension, this
function will not be defined.

If this call is successful, the user's browser will begin to send payment to the `receiver` by resolving
it as a payment pointer and then using SPSP. If `receiver` does not begin with a `$` then it will be queried
as an SPSP endpoint as a URL directly.

The amount of money that the user decides to send is up to them. The user SHOULD pay continuously with time,
and SHOULD only pay when the user has the monetized page active.

This function does not guarantee that the user has paid the server. The backend which runs the SPSP receiver
will have to be queried in order to confirm how much has been paid to a specific receiver.

##### Parameters

| Name | Type | Description |
|:---|:---|:---|
| opts | `Object` | The options for monetization. |
| opts.receiver | `String` | The payment pointer or SPSP endpoint to which ILP payments should be sent. |

##### Returns

`Promise<void>` - A promise which resolves if the user decides to send money to the page.

Rejects with `Error` if the user's browser decides not to send money to this page.
