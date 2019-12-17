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

Each ILP Prepare packet is sent as the body of an HTTP request to the peer's server endpoint. ILP Fulfill or Reject packets are returned as the body of the HTTP response.

## Specification

This is a minimal protocol built on HTTP. HTTP/2 is HIGHLY RECOMMENDED for performance reasons, although HTTP/1.1 MAY also be used. Implementations SHOULD support HTTP version negotiation via Application Protocol Negotiation (ALPN).

### Authentication

Peers MAY use any standard HTTP authentication mechanism to authenticate incoming requests. TLS Client Certificates are RECOMMENDED between peers for security and performance, though bearer tokens such as JSON Web Tokens (JWTs) or Macaroons MAY be used instead. Basic authentication (username and password) is NOT RECOMMENDED, because of the additional delay introduced by securely hashing the password.

### ILP Prepare

#### Request

```http
POST /ilp HTTP/x.x
Host: example.com
Accept: application/octet-stream
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf
Request-Id: 42ee09c8-a6de-4ae3-8a47-4732b0cbb07b
Idempotency-Key: 8988dd17-55e4-40e0-9c57-419d81a0e3a5

< Body: Binary OER-Encoded ILP Prepare Packet >
```

- **Path** &mdash; A connector MAY specify any HTTP path for their peer to send ILP packets to.
- **Host Header** &mdash; The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the Request is sent to.
- **Content-Type / Accept Headers** &mdash; MUST be set to `application/octet-stream`.
- **Request ID Header** &mdash; UUIDv4 to correlate the corresponding ILP Fulfill/Reject with this ILP Prepare, generated from a cryptographically secure source of randomness.
- **Idempotency Key Header** &mdash; UUIDv4 to uniquely identify this packet, generated from a cryptographically secure source of randomness.
- **Body** &mdash; ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### Response

```http
HTTP/x.x 200 OK
```

For backwards compatibility with [RFC 35: ILP over HTTP (draft 2)](https://interledger.org/rfcs/0035-ilp-over-http/draft-2.html), if no `Idempotency-Key` header is included, the raw OER-encoded ILP Fulfill or Reject MUST be returned within the body of the response:

```http
HTTP/x.x 200 OK
Content-Type: application/octet-stream

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

### ILP Fulfill/Reject

#### Request

```http
POST /ilp HTTP/x.x
Host: example.com
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf
Request-Id: 42ee09c8-a6de-4ae3-8a47-4732b0cbb07b
Idempotency-Key: 6ff99499-008e-4499-8644-048450627496

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

- **Path** &mdash; A connector MAY specify any HTTP path for their peer to send ILP packets to.
- **Host Header** &mdash; The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the Request is sent to.
- **Content-Type Header** &mdash; MUST be set to `application/octet-stream`.
- **Request ID Header** &mdash; Request ID from the corresponding ILP Prepare, which is a UUIDv4.
- **Idempotency Key Header** &mdash; UUIDv4 to uniquely identify this packet, generated from a cryptographically secure source of randomness.
- **Body** &mdash; ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### Response

```http
HTTP/x.x 200 OK
```

If the request ID doesn't correspond to an in-flight ILP Prepare, the connector should ignore it and return an error:

```http
HTTP/x.x 400 Bad Request
```

### Error Handling

All semantically valid requests accepted for processing MUST be returned with the HTTP status code `200 OK`, even if the packet is ultimately rejected.

An endpoint MAY return standard HTTP errors, including but not limited to: a malformed or unauthenticated request, rate limiting, or an unresponsive upstream service. Connectors SHOULD relay an ILP Reject packet back to the original sender with an appropriate [Final or Temporary error code](./0027-interledger-protocol-4/0027-interledger-protocol-4#error-codes). Server errors (status codes 500-599) SHOULD be translated into ILP Reject packets with `T00: Temporary Error` codes.

### Idempotence Behavior

Every Interledger packet corresponds to a transaction that may affect financial accounting balances. If a request fails, such as due to a network connection error, retrying ILP requests and responses with [idempotence](https://en.wikipedia.org/wiki/Idempotence) can prevent balance inconsistencies between peers.

To enable this functionality, the two phases of an ILP packet lifecycle are separated into two different HTTP requests: one for the ILP Prepare, and one for the corresponding ILP Fulfill or ILP Reject.

Responses with an HTTP `200 OK` status attest that the packet has been successfully accepted for processing, even if the packet may not necessarily be forwarded. If the connector responds with an HTTP `5xx` or `409 Conflict` status, the client SHOULD retry the request with the same idempotency key.

If no HTTP response is received within a given timeout, clients SHOULD retry sending the packet with the same idempotency key. Clients SHOULD ensure there are multiple attempts to deliver the packet to the peer before the corresponding ILP Prepare expires.

**NOTE:** Clients MUST ensure their peer supports [RFC 35: ILP over HTTP](.) draft 3 or later before retrying ILP Prepare requests to prevent duplicate side effects.

When a connector begins processing an incoming packet with an idempotency key it has not already tracked, it MUST persist that key. If a subsequent request of the same type (ILP Prepare, or ILP Fulfill/Reject) is encountered with the same idempotency key, the packet should be ignored, and the connector should respond with the same `200 OK` status. For safety, the connector MUST persist each idempotency key until the corresponding ILP Prepare expires.

Since ILP Prepare expirations are typically on the order of seconds and the transport layer will handle flow control, exponential backoff and jitter for retries are unnecessary.
