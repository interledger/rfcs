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

Each ILP Prepare packet is sent as the body of an HTTP request to the peer's server endpoint. ILP Fulfill or Reject packets are returned as the body of the HTTP response in the synchronous mode, or sent in a separate HTTP request in the asynchronous mode.

## Specification

This is a minimal protocol built on HTTP. HTTP/2 is HIGHLY RECOMMENDED for performance reasons, although HTTP/1.1 MAY also be used. Implementations SHOULD support HTTP version negotiation via Application Protocol Negotiation (ALPN).

### Authentication

Peers MAY use any standard HTTP authentication mechanism to authenticate incoming requests. TLS Client Certificates are RECOMMENDED between peers for security and performance, though bearer tokens such as JSON Web Tokens (JWTs) or Macaroons MAY be used instead. Basic authentication (username and password) is NOT RECOMMENDED, because of the additional delay introduced by securely hashing the password.

### Send ILP Prepare

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
- **Request Id Header** &mdash; _Optional_. UUIDv4 to correlate the corresponding ILP Fulfill/Reject.
- **Idempotency Key Header** &mdash; _Optional_. UUIDv4 to uniquely identify this packet.
- **Body** &mdash; ILP Prepare encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### Response

In the synchronous mode, the raw OER-encoded ILP Fulfill or Reject is returned within the body of the response:

```http
HTTP/x.x 200 OK
Content-Type: application/octet-stream

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

If the request included a `Request-Id` header, the recipient handling the ILP Prepare SHOULD choose to handle the packet asynchronously and return the corresponding ILP Fulfill/Reject in a separate outgoing HTTP request.

In the asynchronous mode, if the request is semantically valid, the recipient MUST respond immediately that the ILP Prepare is accepted for processing, even if the packet will ultimately be rejected:

```http
HTTP/x.x 202 Accepted
```

#### Retry Behavior

Two peers MAY retry ILP Prepare packets, but MUST both agree to support retries out-of-band to prevent duplicate side effects.

If the recipient of the ILP Prepare responds with an `5xx` or `409 Conflict` status, or no HTTP response is received within a given timeout, the sender of the ILP Prepare SHOULD retry sending the packet with the same idempotency key.

The sender MUST conclude retrying after receiving a response with a `2xx` status, `4xx` error, or receiving the corresponding ILP Fulfill/Reject packet.

The sender SHOULD ensure there are multiple attempts to deliver the packet to the peer before the ILP Prepare expires.

### Async ILP Fulfill/Reject Reply

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
- **Request Id Header** &mdash; Request ID from the corresponding ILP Prepare, which is a UUIDv4.
- **Idempotency Key Header** &mdash; _Optional_. UUIDv4 to uniquely identify this packet.
- **Body** &mdash; ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

#### Response

```http
HTTP/x.x 200 OK
```

If the request ID doesn't correspond to an in-flight ILP Prepare, the connector should ignore it and return an error:

```http
HTTP/x.x 400 Bad Request
```

#### Retry Behavior

If the recipient of the ILP Fulfill/Reject responds with an `5xx` or `409 Conflict` status, or no HTTP response is received within a given timeout, the sender of the ILP Fulfill/Reject SHOULD retry sending the packet with the same idempotency key.

The sender of the ILP Fulfill/Reject MUST conclude retrying after receiving a response with a `2xx` status or `4xx` error.

The sender SHOULD ensure there are multiple attempts to deliver the reply packet to the peer before the corresponding ILP Prepare expires.

### Idempotence

Every Interledger packet corresponds to a transaction that may affect financial accounting balances. If a request fails, such as due to a network connection error, retrying ILP requests and responses with [idempotence](https://en.wikipedia.org/wiki/Idempotence) can prevent balance inconsistencies between peers.

When a connector begins processing an incoming packet with an idempotency key it has not already tracked, it MUST persist that key. If a subsequent request of the same type (ILP Prepare, or ILP Fulfill/Reject) is encountered with the same idempotency key, the packet should be ignored, and the connector should respond with the successful status. For safety, the connector MUST persist each idempotency key until some amount of time after the corresponding ILP Prepare expires so it doesn't accidentally process a duplicate ILP Prepare packet.

### Error Handling

An endpoint MAY return standard HTTP errors, including but not limited to: a malformed or unauthenticated request, rate limiting, or an unresponsive upstream service. Connectors SHOULD relay an ILP Reject packet back to the original sender with an appropriate [Final or Temporary error code](./0027-interledger-protocol-4/0027-interledger-protocol-4#error-codes). Server errors (status codes 500-599) SHOULD be translated into ILP Reject packets with `T00: Temporary Error` codes.
