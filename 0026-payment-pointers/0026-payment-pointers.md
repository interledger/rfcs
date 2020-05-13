---
title: Payment Pointers
draft: FINAL
deprecated: https://paymentpointers.org/
---
# Payment Pointers and Payment Setup Protocols

## Abstract

Payment pointers are a standardized identifier for accounts that are able to receive payments. In the same way that an email address provides an identifier for a mailbox in the email ecosystem a payment pointer is used by an account holder to share the details of their account with anyone that wishes to make a payment to them.

A payment pointer can be resolved to an "https" URL that provides the location of a payment setup service endpoint at which a sender can initiate a payment to the receiver.

## Design Goals

The following design goals are met by this specification:

### Unique and Easily Recognizable

Various standardized and defacto-standardized identifiers are widely used on the Internet today such as email addresses and social media handles. The payment pointer must be obviously unique so that it is not confused with another type of identifier and also so that other identifiers are not assumed to be payment pointers.

### Simple Transcription

It should be easy for someone to exchange their payment pointer with a potential payee either by saying it, writing it down or sending it in a digital message.

### Flexible

The payment pointer should not be tightly coupled to a specific payment setup protocol or protocol version. It should be possible for any new payment setup protocol to leverage payment pointers.

### Widely Usable

It should be simple for individuals or small companies to host their own payment setup protocol receiver endpoints at a URL that can be resolved via a simple and easily recognizable payment pointer. Likewise, it should be possible for a payment services provider to host payment setup protocol receiver endpoints for multiple entities without the risk of hosting them at endpoint URLs that conflict with their other services. To that end the provider should have the option of hosting different receiver endpoints under the same domain and a different path or at a different sub-domain for each receiver.

## Payment Setup Protocols

A payment setup protocol is defined very generically as a protocol for exchanging payment information between a sender and receiver before executing the payment.

An example of a payment setup protocol is the [Simple Payment Setup Protocol](../0009-simple-payment-setup-protocol/) used to setup an Interledger payment.

Payment pointers MUST resolve to an endpoint hosted by a payment receiver at which a payment setup protocol can be initiated. This endpoint is known as the payment setup protocol receiver endpoint.

A payment setup protocol receiver endpoint is identified by an https URL as defined in [RFC7230](https://tools.ietf.org/html/rfc7230#section-2.7.2). It MUST accept HTTP GET requests to initiate the protocol.

Payment setup protocols SHOULD define a custom MIME type for their message definitions and use HTTP content negotiation between the client and endpoint server to determine the payment setup protocol and protocol versions supported by the requesting client and the endpoint server.

Example:

The MIME type for SPSP is: `application/spsp+json`

## Payment Pointer Syntax

This specification uses the Augmented Backus-Naur Form (ABNF) notation of [RFC2234](https://tools.ietf.org/html/rfc2234) and imports the following rules from [RFC3986](https://tools.ietf.org/html/rfc3986#section-3.3)): _host_ and _path-abempty_.

The syntax of a payment pointer is:

```
  "$" host path-abempty
```

Example: `$example.com/bob`

Note that the character set of a payment pointer, as with a valid URL, is limited to valid ASCII characters. Further work may be done to define mappings from other character sets that support international characters (similar to the rules for Internationalized Domain Names) however, such mappings are not defined in this specification. Implementations that attempt to interpret a Payment Pointer that contains non-ASCII characters should be aware of the security risks.

## Payment Setup Protocol Receiver Endpoint Resolution

Given a payment pointer of the form `"$" host path-abempty` the payment setup protocol receiver endpoint URL is:

```
  "https://" host path-abempty
```

If _path-abempty_ is empty or equal to `/` then it is assigned the value `/.well-known/pay`.

Note that this is a restricted profile of the data allowed in a full https URL. Where the URL syntax supports an _authority_ the payment pointer syntax only supports a _host_ which excludes the _userinfo_ and _port_. The payment pointer syntax also excludes the _query_ and _fragment_ parts that are allowed in the URL syntax.

Payment pointers that do not meet the limited syntax of this profile MUST be considered invalid and should not be used to resolve a receiver endpoint.

The resolved endpoint may redirect the client to another URL but the client MUST ensure it affords the sender an opportunity to verify both the originally resolved and ultimate endpoint hosts (See the security risks described below for more details).

Examples:

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

The client should express the protocols it supports by including the media types of the protocol messages in the `Accept` header of the request.

Example:

```
GET /.well-known/pay HTTP/1.1
Host: bob.example.com
Accept: application/spsp+json, application/otherprotocolformat
```

# IANA Considerations

## Well-Known URI

This specification registers a new well-known URI. 

URI suffix:  "pay"

Change controller: Interledger Payments Community Group (W3C)

Specification document(s):  This document

# Security Considerations

Payment pointers have many of the same security risks as URLs so it follows that the security considerations are the same even though payment pointers do not in and of themselves pose a security threat.  

However, as payment pointers are used to provide a compact set of instructions for initiation of a payment, care must be taken to properly interpret the data within a payment pointer, to prevent payments being made to the wrong recipient or leaking of sensitive data.

## Reliability and Consistency

There is no guarantee that once a payment pointer has been used resolve a payment setup protocol receiver endpoint, the same service will be hosted at that URI in the future.

## Semantic Attacks and Phishing

Because payment pointers only support a limited profile of the data in a URL, not all of the attacks described in RFC3986 apply to payment pointers.

However it is possible for a malicious actor to construct a payment pointer that appears to point to a trusted receiver but in fact points to a malicious actor. As a result the pointer is constructed that is intended to mislead a human user by appearing to identify one (trusted) naming authority while actually identifying a different authority hidden behind the noise. 

As detailed in [RFC7230], the "https" scheme (Section 2.7.2) is intended to prevent (or at least reveal) many of these potential attacks on establishing the authority behind a pointer, provided that the negotiated TLS connection is secured and the client properly verifies that the communicating server's identity matches the target URIs authority component (see [RFC2818]).Correctly implementing such verification can be difficult (see [The Most Dangerous Code in the World](#the-most-dangerous-code-in-the-world-validating-ssl-certificates-in-non-browser-software)).

Payment Setup Protocols should take heed of this risk in their design and provide a mechanism for the sender to reliably verify the receiver's identity. This may be as simple as relying on the certificate of the receiving endpoint server to identify the receiver, or may be handled explicitly within the protocol.

Sending clients MUST provide a way for a sender, after providing a pointer to the client, to verify that the entity they are sending to (or at least the entity hosting the payment setup protocol receiver endpoint) is who they intended otherwise senders can easily be fooled into sending money to the wrong receiver. An example of such a mechanism is the use of extended validation certificates at the endpoint.

# References

## The Most Dangerous Code in the World: Validating SSL Certificates in Non-browser Software

Georgiev, M., Iyengar, S., Jana, S., Anubhai, R., Boneh, D., and V. Shmatikov, 
"The Most Dangerous Code in the World: Validating SSL Certificates in Non-browser Software", 
In Proceedings of the 2012 ACM Conference on Computer and Communications Security (CCS'12), pp. 38-49, October 2012,
<http://doi.acm.org/10.1145/2382196.2382204>.


