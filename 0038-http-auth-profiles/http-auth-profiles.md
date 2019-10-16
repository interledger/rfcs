---
title: Interledger HTTP Authentication Profiles
draft: 1
---

# Interledger HTTP Authentication Profiles
A minimal set of extensible, token-based profiles for securing Interledger relationships using HTTP.

## Motivation
Many Interledger protocols and software work well using HTTP. For example, [ILP-over-HTTP]() utilizes HTTP at the [Link Layer](https://interledger.org/rfcs/0001-interledger-architecture/). Additionally, Interledger software often uses HTTP for administrative functionality and other purposes.

This document defines common profiles that can be used to ensure implementations of Interledger software work securely in an interoperable fashion, while simultaneously allowing Interledger software operators to more clearly understand the trade-offs involved with various security choices.

The profiles defined in this RFC should:

* ...be as simple as possible while also being highly secure. 
* ...clearly define any trade-offs involved in choosing a particular profile.
* ...be easily implementable across programming languages in order to aid braod adoption.
* ...utilise well-known and broadly deployed protocols in order to increase confidence the profiles.
* ...be suitable for high-performance use-cases, such as ILPv4 packet processing.
* ...resist replays (emphasis: resist, not necessarily be replay-proof, in order to support high-performance use-cases).
* ...not negate or prevent the ability of operators to layer-on more security on top of a chosen profile.

## Specification

### Overview
This document defines three authentication profiles for securing HTTP network connections in Interledger.

### Authentication
When authenticating requests between Interledger nodes, it is important to choose an algorithm that maintains an appropriate balance between usability and security, while at the same time maintaining high-performance _and_ interoperability.

In order to find this balance, this document defines three Authentication profiles, each with various trade-offs that should be considered before use:

* `SIMPLE`: Allows two ILP nodes to utilize a previously agreed-upon shared-secret as a [Bearer token](https://tools.ietf.org/html/rfc6750) in all ILP-over-HTTP requests. Peers SHOULD consider this token to be opaque and SHOULD NOT derive any special meaning from the token. 

* `JWT_HS_256`: Allows two ILP nodes to utilize a previously agreed-upon shared-secret in order to _derive_ a `Bearer token` that conforms to the JSON Web Token (JWT) specification as defined in [RFC-7519](https://www.rfc-editor.org/rfc/rfc7519.html)

* `JWT_RS_256`: Allows two ILP nodes to utilize public-key pairs to _derive_ a `Bearer token` that conforms to the JSON Web Token (JWT) specification.

Peers MAY use any standard HTTP authentication mechanism to authenticate incoming requests, but SHOULD support `JWT_HS_256` at a minimum. It is RECOMMENDED to use `JWT_RS_256` for production deployments.

#### `SIMPLE` Authentication Profile
This profile allows two ILP nodes to utilize a previously agreed-upon shared-secret that contains at least 32 bytes (256 bits) of randomly generated data, and is encoded using Base64.

Because tokens in this profile do not inherently contain information about the identity of the caller, requests MUST contain an additional HTTP request-header named `Auth-Principal`.
 
This extra header allows for the identity of the authentication request to be separated from authentication token itself, which reduces computational overhead as well as data-management complexity (e.g., implementations do not need to create data-store indexes using derivations of tokens for lookup purposes).

##### Example Usage
An example shared-secret in this profile is `HEiMCp0FoAC903QHueY89gAWJHo/izaBnJU8/58rlSI=`. This shared secret is passed as an `Authorization` header in each HTTP request, using the Bearer token scheme, along with an `Auth-Principal` header like this: 

```
Auth-Principal: alice-usd-123
Authorization: Bearer HEiMCp0FoAC903QHueY89gAWJHo/izaBnJU8/58rlSI=
``` 

Implementations MAY support this profile, but SHOULD consider it for development purposes only.
 
##### Trade-off Summary
* **Pros**
  * The simplest, most usable Authentication profile -- just a shared-secret with _at least_ 32 bytes and an identity header.
  * Very little processing time to verify a token (Note that token verification in this mode should utilize a Constant Time Comparison to avoid [Timing Attacks](https://en.wikipedia.org/wiki/Timing_attack)))

* **Cons**
  * The shared-secret is transmitted "on the wire" for every request, increasing the chances that it might be intercepted by a compromised TLS session (e.g., a [MITM attack](https://en.wikipedia.org/wiki/Man-in-the-middle_attack)); a TLS termination endpoint (e.g., a Load Balancer); or logged by an internal system during transit.
  * The shared-secret itself never expires, so if an implementation neglects to rotate the secret with its peer, this token will likely be very long-lived. This increases the chance of compromise by an attacker, and means compromised usage of this type of token could go undetected for very longer periods of time.
  * Requires out-of-band communication for both peers to agree upon the shared secret.

#### `JWT_HS_256` Authentication Profile
This profile allows two ILP nodes to utilize a previously agreed-upon shared-secret, but then derive an [RFC-7519](https://tools.ietf.org/html/rfc7519) compliant JWT token in order to perform actual authentication.

##### JWT Claims
In order to be considered a valid JWT for this profile, the signed JWT MUST contain a `sub` (subject) claim containing the identifier of the "principal" that the token authenticates.

A JWT token SHOULD also include an `exp` (expiry) claim that indicates a date/time after which the token should be considered invalid. Implementations SHOULD reject any tokens with a missing or invalid expiry claim. 

Note that tokens without this claim never expire, and only become invalid if the shared-secret used to sign the JWT changes or is otherwise invalidated.

##### Example Usage
In this profile, the JWT is passed as an `Authorization` header in each HTTP request, using the [Bearer token](https://tools.ietf.org/html/rfc6750) scheme. 

One example of such a Bearer token:

`Authorization: Bearer eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJzdWIiOiJhbGljZSJ9._Jn0pkqrK1leE3WZJKn-g5hm5kGJxGdSHggtz5wO1w4`. 

Using the JWT specification, this token can be verified using the shared-secret previously agreed upon. For example, the above token contains a `sub` claim of `alice` and can be verified using a shared-secret value of `HEiMCp0FoAC903QHueY89gAWJHo` (Base64 encoded).

Another example is a Bearer token that contains an expiration date:

`Authorization: Bearer eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJzdWIiOiJhbGljZSIsImV4cCI6MTU1ODAzNTg2OH0.__9CiSGdn4Grhl48slun7Lp4q4xt0uq398omcipBU8M`. 

Using the JWT specification, this token can be verified using the shared-secret previously agreed upon. For example, the above token contains a `sub` claim of `alice` and an `exp` claim of `1558035868`, which means this token is no longer valid after `May 16th, 2019 at 9:29:11 GMT`. This token can be verified using a shared-secret value of `HEiMCp0FoAC903QHueY89gAWJHo` (Base64 encoded).

##### Trade-off Summary
* **Pros**
  * Allows both identity and authentication claims to be contained in single Bearer token, which eliminates the need for a second `Auth-Principal` header.
  * Requires only enough processing to perform an HMAC-SHA256 signing operation, which is very fast.
  * Supports token expiry, which allows tokens to be generally short-lived so that peers can narrow the potential window of unauthorized usage in the event of token compromise.
  * The actual shared-secret is _never_ transmitted "on the wire" during any request. Instead, authentication tokens are always _derived_ from the shared-secret, which eliminates the risk of an _actual_ shared-secret being intercepted  in transit.

* **Cons**
  * More complex than the `SIMPLE` profile.
  * Potentially more computation required due to SHA-256 calculations and JSON serialization/deserialization (though this is somewhat muted if short-lived tokens are re-used across multiple requests).
  * Total transmitted bytes for authentication are more than the `SIMPLE` scheme (about 41 bytes, or ~50% more). However, HTTP/2 header compression should mitigate this differential.
  * Requires out-of-band communication for both peers to agree upon the shared secret.

#### `JWT_RS_256` Authentication Profile
This profile allows two ILP nodes to utilize public/private key pairs and an asymmetric signature scheme to generate and verify auth tokens. This requires one private key be used to sign a given JWT, with a different public key used to verify the signature. The specific algorithm for this profiles is `RS_256` as defined in [RFC-7518](https://www.rfc-editor.org/rfc/rfc7518#section-3.3). 

##### JWT Claims
In order to be considered a valid JWT for this profile, a signed JWT MUST contain the following claims:
 
 * `iss` (issuer): A claim that claim identifies the principal that issued the JWT. See [Section 4.1.1 of RFC-7519](https://www.rfc-editor.org/rfc/rfc7519.html#section-4.1.1) for more details.
 * `sub` (issuer): A claim that claim identifies the principal that is the subject of the JWT. See [Section 4.1.2 of RFC-7519](https://www.rfc-editor.org/rfc/rfc7519.html#section-4.1.2) for more details.
 * `aud` (audience): A claim that claim identifies the recipients that the JWT is intended for. See [Section 4.1.3 of RFC-7519](https://www.rfc-editor.org/rfc/rfc7519.html#section-4.1.3) for more details.
 * `exp` (expiry): A claim that indicates a date/time after which the token should be considered invalid. Implementations SHOULD reject any tokens with a missing or invalid expiry claim.  See [Section 4.1.4 of RFC-7519](https://www.rfc-editor.org/rfc/rfc7519.html#section-4.1.4) for more details.

##### Example Usage
In this profile, the JWT is passed as an `Authorization` header in each HTTP request, using the [Bearer token](https://tools.ietf.org/html/rfc6750) scheme. 

One example of such a Bearer token:

`Authorization: Bearer eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJodHRwczovL2V4bWFwbGUuY29tIiwic3ViIjoiaHR0cHM6Ly9leGFtcGxlLmNvbS9hbGljZSIsImF1ZCI6Imh0dHBzOi8vZXhhbXBsZS5jb20vYm9iIiwiZXhwIjoxNTE2MjM5MDIyfQ.Vpa0XsMzFU95hPHhKYt8cd4HwbUz3F2Wt8tLXEkRZoU_z4xwktrfUxlrfOXZ5PxyVboDSZfNvUNhYawCx87M64JIyYDxGJbj1piu7m6F9_P3Qoi-h0bHmkk_K5x-CnFPqxBVhnWaqQFh3hzSzf0IHNJz5YMeZi4Mxgfxys-xcVKSrgel8xxMME4ns961ec49LurPpkvXIhXqsGXyBglgAe9tQBIpY-rbaq4dCLgHp6h2MFt-6h0z2HZ2B__uprRVoOOnK6s1-xQjS5wbKf7tez9u6o5ati2KjC94z8pOxG-OaCC4bW6G3aKjFwOtv4Xd-Qda1W37kda1cv4bb-qadg`. 

Using the JWT specification, this token can be verified using the public-key that corresponds to the private key that signed the token. For example, the above token contains the following claims:

* `iss`: "https://idp.exmaple.org",
* `sub`: "https://example.com/alice",
* `aud`: "https://example.com/bob",
* `exp`: 1516239022

The token can be verified using the following public-key, which in a production deployment might be advertised at a TLS-encrypted endpoint conforming to [RFC-7517](https://tools.ietf.org/html/rfc7517):
 
 ```
ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQC0H891JhR+Stgx81JyZeU48F4VUAS7E/OKvaVG5OjE9c+iIp2WcYFHqWjeBfrcPS1ADnTbxiKDd5D7EGWLDkBGha9H7m2hH/4PhywHomltp4Z1W7HJISzIS5JvPWFctKeKmhEekMi24yhtf44NkZg2zQijzLMQuxfaPGoW/88omtuDVaqQUmt3/Vx3v8D5ejQ2N8p7BrvpiUPQy+ZakAJf7MG0+EnaCjgnGAc9Q9wEBgMq6ifAENLne6BtQvA34jiWEIGDuD/veUwe0r0Ao/ZipZfcRJKybYNHbs5YQoxXOI2qo8qPwFrF2AJzak8+MwaiFYrDzGk8nV3e3i38RH0p test@example.com
 ```

##### Trade-off Summary
* **Pros**
  * Similar benefits to the `JWT_HS_256` profile, but more securely supports the issuer claim because each party signs tokens with its own private key. This allows token verifiers to know exactly who generated the token, including allowing for 3rd-party signing.
  * Supports token expiry, which allows tokens to be generally short-lived so that peers can narrow the potential window of unauthorized usage in the event of token compromise.
  * Allows for asymmetric key rotation without forcing a peer to change a shared-secret. 

* **Cons**
  * More complex than the `SIMPLE` and `JWT_HS_256` profile.
  * Total transmitted bytes for authentication are more than the `SIMPLE` and `JWT_HS_256` schemes. However, HTTP/2 header compression should mitigate this differential as well.
  * Requires out-of-band communication for both peers to agree upon public keys.
  * Verification performance is slower than the `SIMPLE` and `JWT_HS_256` profile`.

### Authorization
The `HS-256` and `RS_256` profiles defined in this RFC rely upon signed JWTs, which support arbitrary claims that can be used for authorization decisions. This document does not define any authorization-specific primitives, although implementations MAY use various authentication claims in order to inform authorization decisions.

## Appendix1: Security Best Practices
This section outlines and clarifies some best practices for authentication-token security when using this protocol. Recommendations in this section are _Non-Normative_, but highly RECOMMENDED.

### Follow Standardized Security Recommendations
It is advisable to follow all applicable best practices when using a Bearer-token scheme for authentication. [Section 5.1 of RFC-6570](https://tools.ietf.org/html/rfc6750#section-5) contains a number of good practices that should be considered on a per-deployment basis. 

### Use SIMPLE Profile for Development/Testing Only
The `SIMPLE` authentication profile provides only marginal benefits when compared to the `JWT_HS_256` profile, but introduces significant drawbacks as outlined in the "Trade-off Summary" sections of this RFC. As such, the `SIMPLE` profile MAY be used for development or testing purposes, but SHOULD NOT be used in production scenarios. Instead, prefer `JWT_HS_256` for production deployments.

### Avoid HTTP Basic and Form-based Auth
HTTP Auth schemes using a username and password are NOT RECOMMENDED for the same reasons that the `SIMPLE` profile is only recommended for development and testing scenarios.
 
### Use Reasonable Token Expiries
Tokens generators should choose a reasonable token expiry. Considerations in this choice include the ability to cache and re-use tokens for a limited time in order to enable very fast authentication decisions. However, this should be balanced against a desire for shorter token lifetimes, which will limit the attack surface caused by a compromised token.

As a best practice, implementations SHOULD use tokens that expire. For example, consider generating tokens with a lifetime that doesn't exceed 5 minutes.

### Secrets At Rest
Implementations SHOULD protect secret-values that can be used to generate authentication tokens by encrypting them prior to storage. This will help prevent actual shared-secrets or other sensitive data from being captured by unauthorized parties, increasing the chances that only Interledger software will be able to generate tokens.
  
### Secrets In Memory
Implementations SHOULD minimize the amount of time that an actual secret-value exists in-memory in unencrypted form. This includes narrowing the availability of secrets to only code that actually requires them; minimizing the time any secret might exist in memory; and zeroing out memory after a secret is no longer used, if possible. 

### Mutual TLS
All Interledger connections MUST be performed over a TLS session. However, it is also RECOMMENDED to use TLS Client Certificates between peers for additional security. 
  
### High Security Deployments
For deployments requiring very high security, it is recommended to utilize a secret-store deployed outside of the Interledger software runtime, such as a "key management service" and/or "hardware key storage." 

This will provide an extra layer of protection in the event that a runtime is compromised, and will also make it significantly harder for an attacker to compromise actual shared-secret or private key values (especially if employing an HSM). 

However, before employing such a system, operators SHOULD perform extensive performance testing to ensure proper levels of service.
 
## Appendix2: Normative References
For more details on the algorithms and standards referenced in this RFC, see the following:

* RFC-6750: [Bearer Token Usage](https://tools.ietf.org/html/rfc6750)
* RFC-7518: [JSON Web Algorithms (JWA)](https://www.rfc-editor.org/rfc/rfc7518.html)
* RFC-7519: [JSON Web Token (JWT)](https://www.rfc-editor.org/rfc/rfc7519.html)
