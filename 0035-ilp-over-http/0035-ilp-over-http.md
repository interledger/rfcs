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

### Request

```http
POST /ilp HTTP/x.x
Host: example.com
Accept: application/octet-stream
Content-Type: application/octet-stream
Authorization: Bearer zxcljvoizuu09wqqpowipoalksdflksjdgxclvkjl0s909asdf

< Body: Binary OER-Encoded ILP Prepare Packet >
```

**Field Details:**

- **Path** - A connector MAY specify any HTTP path for their peer to send ILP packets to.
- **Host Header** - The standard [HTTP Host Header](https://tools.ietf.org/html/rfc2616#section-14.23) indicating the domain of the HTTP server the Request is sent to.
- **Content-Type / Accept Headers** - MUST be set to `application/octet-stream`.
- **Body** - ILP Packet encoded using OER, as specified in [RFC 27: Interledger Protocol V4](./0027-interledger-protocol-4/0027-interledger-protocol-4.md).

### Response

```http
HTTP/x.x 200 OK
Content-Type: application/octet-stream

< Body: Binary OER-Encoded ILP Fulfill or Reject Packet >
```

All ILP Packets MUST be returned with the HTTP status code `200: OK`.

An endpoint MAY return standard HTTP errors, including but not limited to: a malformed or unauthenticated request, rate limiting, or an unresponsive upstream service. Connectors SHOULD either retry the request, if applicable, or relay an ILP Reject packet back to the original sender with an appropriate [Final or Temporary error code](./0027-interledger-protocol-4/0027-interledger-protocol-4#error-codes). Server errors (status codes 500-599) SHOULD be translated into ILP Reject packets with `T00: Temporary Error` codes.

