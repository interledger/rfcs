---
title: Payment Pointers
draft: 1
---
# Payment Pointers and Payment Setup Protocols

## Abstract

Payment pointers are a standardized identifier for accounts that are able to recieve payments. In the same way that an email address provides an identifier for a mailbox in the email ecosystem a payment pointer is used by an account holder to share the details of their account with anyone that wishes to make a payment to them.

A payment pointer can be normalized to an "https" URL that provides the location of a payment setup service endpoint at which a sender can initiate a payment to the receiver.

## Design Goals

The following design goals are met by this specification:

### Unique and Easily Recognizable

Various standardized and defacto-standardized identifiers are widely used on the Internet today such as email addresses and social media handles. The payment pointer must be obviously unique so that it is not confused with another type of identifier and also so that other identifiers are not assumed to be payment pointers.

### Simple Transcription

It should be easy for someone to exchange their payment pointer with a potential payee either by saying it, writing it down or sending it in a digital message.

### Flexible

The payment pointer should not be tightly couple to a specific payment setup protocol or protocol version. It should be possible for any new payment setup protocol to leverage payment pointers.

### Widely Usable

It should be simple for individuals or small companies to host their own payment setup protocol receiver endpoints at a URL that can be resolved via a simple and easily recognizable payment pointer. Likewise, it should be possible for a payment services provider to host payment setup protocol receiver endpoints for multiple entities without the risk of hosting them at endpoint URLs that conflict with their other services. To that end the provider should have the option of hosting different receivier endpoints under the same domain and a different path or at a different subdomain for each receiver.

## Payment Setup Protocols

A payment setup protocol is defined very generically as a protocol for exchanging payment information between a sender and receiver before executing the payment.

An example of a payment setup protocol is the [Simple Payment Setup Protocol](https://interledger.org/rfcs/0009-simple-payment-setup-protocol/) used to setup an Interledger payment.

Payment pointers MUST resolve to an endpoint hosted by a payment receiver at which a payment setup protocol can be initiated. This endpoint is known as the payment setup protocol receiver endpoint.

A payment setup protocol receiver endpoint is identified by an https URL as defined in [RFC7230](https://tools.ietf.org/html/rfc7230#section-2.7.2). It MUST accept HTTP GET requests to initiate the protocol.

Payment setup protocols SHOULD define a custom MIME type for their message definitions and use HTTP content negotitation between the client and endpoint server to determine the payment setup protocol and protocol versions supported by the requesting client and the endpoint server.

## Payment Pointer Syntax

This specification uses the Augmented Backus-Naur Form (ABNF) notation of [RFC2234](https://tools.ietf.org/html/rfc2234) and imports the following rules from [RFC3986](https://tools.ietf.org/html/rfc3986#section-3.3)): _host_ and _path-abempty_.

The syntax of a payment pointer is:

```
  "$" host path-abempty
```

## Payment Setup Protocol Receiver Endpoint Resolution

Given a payment pointer of the form `"$" host path-abempty` the payment setup protocol receiver endpoint URL is:

```
  "https://" host path-abempty
```

If _path-abempty_ is empty then it is assigned the value `/.well-known/pay`.

Note that this is a restrcited profile of the data allowed in a full https URL. Where the URL syntax supports an _authority_ the payment pointer syntax only supports a _host_ which excludes the _userinfo_ and _port_. The payment pointer syntax also excludes the _query_ and _fragment_ parts that are allowed in the URL syntax.

### Examples

The following payment pointers resolve to the specified endpoint URLS:

```
$example.com ->                https://example.com/.well-known/pay
$example.com/invoices/12345 -> https://example.com/invoices/12345
$bob.example.com ->            https://bob.example.com/.well-known/pay
$example.com/bob ->            https://example.com/bob
```

# Payment Initiation

Given a payment pointer for a receiver, a sending client should resolve the https URL of the payment setup protocol receiver endpoint according to the rules defined in this specification.

The client should then initiate an https connection with the endpoint server and perform an http GET request to the endpoint URL.

The cleint should express the protocols it supports by including the media types of the protocol messages in the `Accept` header of the request.

# IANA Considerations

## Well-Known URI

This specification registers a new well-known URI. 

URI suffix:  "pay"

Change controller:  Interledger Payments Community Group (W3C)

Specification document(s):  This document

# Security Considerations

Payment pointers have many of the same security risks as URLs so it follows that the security considerations are the same even though payment pointers do not in and of themselves pose a security threat.  

However, as payment pointers are used to provide a compact set of instructions for initiation of a payment, care must be taken to properly interpret the data within a payment pointer, to prevent payments being made to the worng recipient or leaking of sensitive data.

## Reliability and Consistency

There is no guarantee that once a payment pointer has been used resolve a payment setup protocol receiver endpoint, the same service will be hosted at that URI in the future.

## Semantic Attacks and Phishing

Because payment pointers only support a limited profile of the data in a URL, not all of the attacks described in RFC3986 apply to payment pointers.

However it is possible for a malicious actor to construct a payment pointer that appears to point to a trusted receiver but in fact poimnts to a malicious actor. This is especially so when using internationalized domain names in the payment pointer as these can be constcuted to appear as if there is a path separator (`/`) but this may in fact be a non-latin character in the _host_ portion of the pointer.

As a result the pointer is constructed that is intended to mislead a human user by appearing to identify one (trusted) naming authority while actually identifying a different authority hidden behind the noise. 

As detailed in [RFC7230], the "https" scheme (Section 2.7.2) is intended to prevent (or at least reveal) many of these potential attacks on establishing the authority behind a pointer, provided that the negotiated TLS connection is secured and the client properly verifies that the communicating server's identity matches the target URI's authority component (see [RFC2818]).Correctly implementing such verification can be difficult (see [Georgiev]).

Payment Setup Protocols should take heed of this risk in their design and provide a mechainsim for the sender to reliably verify the receiver's identity. This may be as simple as relying on the certificate of the receving endpoint server to identify the receiver, or may be handled explicitly within the protocol.

[Georgiev]    Georgiev, M., Iyengar, S., Jana, S., Anubhai, R.,
                 Boneh, D., and V. Shmatikov, "The Most Dangerous Code
                 in the World: Validating SSL Certificates in Non-
                 browser Software", In Proceedings of the 2012 ACM
                 Conference on Computer and Communications Security (CCS
                 '12), pp. 38-49, October 2012,
                 <http://doi.acm.org/10.1145/2382196.2382204>.