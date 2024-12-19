---
title: ILP Over HTTP
type: working-draft
draft: 3
---

# ILP Over HTTP

> A bilateral communication protocol for server-to-server connections

## Motivation

Scaling Interledger infrastructure to handle large volumes of ILP packets requires horizontally scaling connectors. Using HTTP for bilateral communication enables service providers to leverage standard tools and services for hosting, load balancing, Distributed Denial of Service (DDoS) protection, and monitoring.

## Overview

In an ILP Over HTTP connection, both peers run HTTP servers with accessible HTTPS endpoints. When peering, the peers exchange their respective URLs, authentication tokens or TLS certificates, ILP addresses, and settlement-related details.

Each ILP Prepare packet is sent as the body of an HTTP request to the peer's server endpoint. The peer asynchronously returns ILP Fulfill or Reject packets in the body of a separate HTTP request. 

> **Note:** Returning ILP Fulfill or Reject packets synchronously in the HTTP response body of the original ILP Prepare request is considered deprecated.


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
- **Body** &mdash; ILP Prepare encoded using OER, as specified in [RFC 27: Interledger Protocol V4](../0027-interledger-protocol-4/0027-interledger-protocol-4.md).
- **Prefer** &mdash; SHOULD be set to `respond-async` for backwards compatibility with recipients supporting [synchronous ILP over HTTP](#deprecated-synchronous-mode).
- **Callback URL Header** &mdash; Callback URL of the origin connector to send an HTTP request with the ILP Fulfill/Reject. Required unless peers exchange the callback URL out-of-band.
- **Request Id Header** &mdash; UUIDv4 to uniquely identify this ILP Prepare, and correlate the corresponding ILP Fulfill/Reject.

#### Response

If the request is semantically valid, the recipient MUST respond immediately that the ILP Prepare is accepted for processing, even if the packet will ultimately be rejected:

```http
HTTP/x.x 202 Accepted
```

If the recipient handling the ILP Prepare supports both [synchronous mode](#deprecated-synchronous-mode) and the standard asynchronous mode, they SHOULD handle the packet asynchronously if the request includes a `Prefer: respond-async` header.

### ILP Fulfill/Reject Reply

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
- **Body** &mdash; ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](../0027-interledger-protocol-4/0027-interledger-protocol-4.md).

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

The sender of the ILP Prepare should only process the first ILP reply they receive corresponding to the original ILP Prepare packet.

### [Deprecated] Synchronous Mode

Each ILP Prepare packet is sent as the body of an HTTP request to the peer's server endpoint. In synchronous ILP over HTTP, ILP Fulfill or Reject packets are returned as the body of the HTTP response.

#### ILP Prepare Request

```http
POST /ilp HTTP/x.x
Host: bob.example
Accept: application/octet-stream
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf

< Body: Binary OER-Encoded ILP Prepare Packet >
```

- **Path** &mdash; A connector MAY specify any HTTP path for their peer to send ILP packets to.
- **Host Header** &mdash; The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the request is sent to.
- **Content-Type / Accept Headers** &mdash; MUST be set to `application/octet-stream`.
- **Body** &mdash; ILP Prepare encoded using OER, as specified in [RFC 27: Interledger Protocol V4](../0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### ILP Fulfill/Reject Response

The raw OER-encoded ILP Fulfill or Reject is returned within the body of the response:

```http
HTTP/x.x 200 OK
Content-Type: application/octet-stream

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

### Error Handling

An endpoint MAY return standard HTTP errors, including but not limited to: a malformed or unauthenticated request, rate limiting, or an unresponsive upstream service. Connectors SHOULD relay an ILP Reject packet back to the original sender with an appropriate [Final or Temporary error code](../0027-interledger-protocol-4/0027-interledger-protocol-4.md#error-codes). Server errors (status codes 500-599) SHOULD be translated into ILP Reject packets with `T00: Temporary Error` codes.
