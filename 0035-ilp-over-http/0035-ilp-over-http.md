---
title: ILP Over HTTP
draft: 2
---

# ILP Over HTTP

> A bilateral communication protocol for server-to-server connections

## Motivation

Scaling Interledger infrastructure to handle large volumes of ILP packets requires horizontally scaling connectors. Using HTTP for bilateral communication enables service providers to leverage standard tools and services for hosting, load balancing, Distributed Denial of Service (DDoS) protection, and monitoring.

## Overview

In an ILP Over HTTP connection, both peers run HTTP servers with accessible HTTPS endpoints. When peering, the peers exchange their respective URLs, authentication tokens or TLS certificates, ILP addresses, and settlement-related details.

Each ILP Prepare packet is sent as the body of an HTTP request to the peer's server endpoint. ILP Fulfill or Reject packets are returned as the body of the HTTP response in synchronous mode, or sent in a separate HTTP request in asynchronous mode.

## Specification

This is a minimal protocol built on HTTP. HTTP/2 is HIGHLY RECOMMENDED for performance reasons, although HTTP/1.1 MAY also be used. Implementations SHOULD support HTTP version negotiation via Application Protocol Negotiation (ALPN).

### Authentication

Peers MAY use any standard HTTP authentication mechanism to authenticate incoming requests. TLS Client Certificates are RECOMMENDED between peers for security and performance, though bearer tokens such as JSON Web Tokens (JWTs) or Macaroons MAY be used instead. Basic authentication (username and password) is NOT RECOMMENDED, because of the additional delay introduced by securely hashing the password.

### Send ILP Prepare

#### Request

```http
POST /ilp HTTP/x.x
Host: bob.example
Accept: application/octet-stream
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf
Prefer: respond-async
Callback-Url: https://alice.example/incoming/ilp
Request-Id: 42ee09c8-a6de-4ae3-8a47-4732b0cbb07b

< Body: Binary OER-Encoded ILP Prepare Packet >
```

- **Path** &mdash; A connector MAY specify any HTTP path for their peer to send ILP packets to.
- **Host Header** &mdash; The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the request is sent to.
- **Content-Type / Accept Headers** &mdash; MUST be set to `application/octet-stream`.
- **Body** &mdash; ILP Prepare encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

Asynchronous mode uses these additional headers:

- **Prefer** &mdash; MUST be set to `respond-async`. If omitted, the reply behavior defaults to synchronous mode.
- **Request Id Header** &mdash; UUIDv4 to uniquely identify this ILP Prepare, and correlate the corresponding ILP Fulfill/Reject.
- **Callback URL Header** &mdash; Callback URL of the origin connector to send an asynchronous HTTP request with the ILP Fulfill/Reject. Required unless peers exchange the callback URL out-of-band.

#### Response

In synchronous mode, the raw OER-encoded ILP Fulfill or Reject is returned within the body of the response:

```http
HTTP/x.x 200 OK
Content-Type: application/octet-stream

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

If the request includes a `Prefer: respond-async` header, the recipient handling the ILP Prepare SHOULD choose to handle the packet asynchronously and return the corresponding ILP Fulfill/Reject in a separate outgoing HTTP request.

If the request is semantically valid and the recipient chooses to handle it asynchronously, they MUST respond immediately that the ILP Prepare is accepted for processing, even if the packet will ultimately be rejected:

```http
HTTP/x.x 202 Accepted
```

### Async ILP Fulfill/Reject Reply

#### Request

```http
POST /incoming/ilp HTTP/x.x
Host: alice.example
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf
Request-Id: 42ee09c8-a6de-4ae3-8a47-4732b0cbb07b

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

- **Path** &mdash; HTTP path from the callback URL in the original request carrying the ILP Prepare.
- **Host Header** &mdash; The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the Request is sent to.
- **Content-Type Header** &mdash; MUST be set to `application/octet-stream`.
- **Request Id Header** &mdash; Request ID from the corresponding ILP Prepare, which is a UUIDv4, matching this reply to the original request.
- **Body** &mdash; ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### Response

```http
HTTP/x.x 200 OK
```

If the request ID doesn't correspond to an in-flight ILP Prepare, or a reply was already processed, the connector should ignore it and return an error:

```http
HTTP/x.x 400 Bad Request
```

#### Retry Behavior

If the recipient of the ILP Fulfill/Reject responds with a `5xx` status or no HTTP response is received within a given timeout, the sender of the ILP Fulfill/Reject SHOULD retry sending the request.

The sender of the ILP Fulfill/Reject MUST conclude retrying after receiving a response with a `2xx` status or `4xx` error.

The sender of the ILP Fulfill/Reject SHOULD ensure there are multiple attempts to deliver the reply packet to the peer before the corresponding ILP Prepare expires.

#### Idempotence

An ILP Fulfill packet corresponds to a commitment which affects financial accounting balances. If an HTTP request carrying the ILP reply fails, such as due to a network connection error, retrying delivery of the ILP reply with [idempotence](https://en.wikipedia.org/wiki/Idempotence) can prevent balance inconsistencies between peers.

If the sender of an ILP Prepare expects an asynchronous reply, they should only process the first ILP reply they receive corresponding to the in-flight ILP Prepare.

### Error Handling

An endpoint MAY return standard HTTP errors, including but not limited to: a malformed or unauthenticated request, rate limiting, or an unresponsive upstream service. Connectors SHOULD relay an ILP Reject packet back to the original sender with an appropriate [Final or Temporary error code](./0027-interledger-protocol-4/0027-interledger-protocol-4#error-codes). Server errors (status codes 500-599) SHOULD be translated into ILP Reject packets with `T00: Temporary Error` codes.
