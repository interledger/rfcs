---
title: Interledger Tokens
draft: 1
---
# Interledger Tokens

An **Interledger Token** is a special form of JSON Web Token that can be used to initiate an Interledger payment. The token provides proof that the payment has been pre-authorized by the payer. By using these tokens new use cases for "debit pull" style payments such as recurring subscriptions or offline authorization are possible.

## Background

TODO

## Motivation

TODO

## Terminology

The following terms are used throughout this specification. Where they are used their meaning as follows:

### Payer

The entity whose funds are being spent when the token is used to initiate a payment.

### Payer's Interledger Service Provider (ILSP)

The entity that accepts and processes the token and payment request. This may be the payer or they may delegate it to some other entity that is able to make payments on their behalf.

### Payee

The entity that is requesting payment using the token.

## The Interledger Token

An **Interledger Token** is a special form of a JSON Web Token (JWT) [RFC7519](https://tools.ietf.org/html/rfc7519) that can be submitted to a participant on the Interledger network to request that they initiate a new payment via ILP. The content of the token describes how much to pay, who to pay and provides information for the entity processing the token to verify that the payment was authorized by the owner of the funds being sent.

**Interledger Tokens** are limited profile of a standard JWT. This profile limits the allowed algorithms, allowed claims and defines specific rules for what constitutes valid claim values. A token is used by a payee to "claim" that a payment has been authorized by the payer in accordance with the terms of the token.

After processing a token and making a payment the participant that has made the payment MAY return a new token to the payee to use again in the future. For example, a payee may posses a token that authorizes a payment to them of USD 100. They may then submit this to initiate a payment but request that only USD 25 is sent in the payment. Following successful execution of the payment they may be returned a new token that authorizes a payment to them of USD 75.

An example token payload is shown below (with further details provided in later sections):

```json
{
  "jti": "48359d89-e9ef-44dd-9a3d-68f991ed7556", //Unique Token ID
  "iss": "872369652347412343", //Unique identifier for the payer (recognized by their ILSP)
  "sub": "example.payee123", //ILP Address of the payee
  "aud": "https://superwallet.example/ilp/", //Endpoint to which the token is submitted
  "exp": "1518699103", //The Expiry of the token (Thursday, February 15, 2018 12:51:43 PM)
  "payee": {
    "max": "100", //The maximum amount that should be delivered to the payee when this token is presented 
    "min": "0", //The minimum amount that should be delivered to the payee when this token is presented
    "asset": "USD", //The asset that the min and max values are denominated in
    "scale": "2" //The scale of the min and max (eg. if scale = 2 then a value of 1234 = USD 12.34)
  },
  "payer": {
    "protected":"eyJhbGciOiJkaXIiLCJlbmMiOiJBMjU2R0NNIn0=", // BASE64URL({"alg":"dir","enc":"A256GCM"})
    "iv":"48V1_ALb6US04U3b", //Random 96-bit IV
    "ciphertext":"5eym8TW_c8SuK0ltJ3rpYIzOeDQz7TALvtu6UG9oMo4vpzs9tX_EFShS8iB7j6ji
     SdiwkIr3ajwQzaBtQD_A", //Data for the payer's ILSP encrypted using AES GCM and pre-shared key
    "tag":"XFBoMYUZodetZdvTiFvSkQ" //Authentication Tag
  }
}
```
The `payer` is a JSON Web Encryption (JWE) object (See [RFC7516]](https://tools.ietf.org/html/rfc7516)) containing data that is securely exchanged between the payer and the payer's ILSP. The plain-text representation of `payer.ciphertext` in this example is:

```json
{
  "max": "100", //The maximum amount that must be sent from the payer's account when this token is presented.
  "min": "0", //The minimum amount that must be sent from the payer's account when this token is presented.
  "asset": "USD", //The asset that must be spent when making a payment from the payer's account. (In the event that the payer holds multiple accounts with the ILSP)
  "scale": "2", //The scale of the max and min amounts above
}
```

The payee can POST this token to `https://superwallet.example/ilp/` to initiate the process of making ILP payments to `example.payee123.tx567`.

### Valid Headers

Only the following header values are allowed in an **Interledger Token**:

| Header | Name      | Description                               |
|--------|-----------|-------------------------------------------|
| alg    | Algorithm | The algorithm used to sign the token body |

### Valid Header Values

Only the following header values are allowed in an **Interledger Token**:

| Header | Value | Description                                                                                     |
|--------|-------|-------------------------------------------------------------------------------------------------|
| alg    | HS256 | HMAC using SHA-256 (See [RFC7518 Section 3.2](https://tools.ietf.org/html/rfc7518#section-3.2)) |

### Valid Claims

The following Registered Claim Names (as defined in RFC7519) are allowed in an **Interledger Token**:

| Claim | Name            | Description |
|-------|-----------------|-------------|
| jti   | Token ID        | The unique identifier of the token. This must unique per payer (issuer). |
| iss   | Issuer          | An identifer for the payer that can will allow the Payer's ILSP to uniquely identify the payer. |
| sub   | Subject         | The ILP address of the payee. |
| aud   | Audience        | The URL of the **token submission endpoint** of the Payer's ILSP. Only a valid HTTPS URL is allowed with no query string or fragment portions. |
| exp   | Expiration Time | The expiry time of the token (per [RFC7519](https://tools.ietf.org/html/rfc7519)). |
| nbf   | Not Before      | The time before which the token may not be used (per [RFC7519](https://tools.ietf.org/html/rfc7519)). |
| iat   | Issued At       | The time at which the JWT was issued (per [RFC7519](https://tools.ietf.org/html/rfc7519). |

The following Public Claim Names (as defined in RFC7519) are allowed in an **Interledger Token**. These will be registered with IANA in accordance with the process defined in RFC7519:

| Claim | Name       | Description |
|-------|------------|-------------|
| payee | Payee Data | Data about the payment that can be made with this token as relates to the account of the payee. |
| payer | Payer Data | Data about the payment that can be made with this token as relates to the account of the payer. |

#### Payer and Payee Data

The Payer Data and Payee Data contain the same fields however the Payee Data is un-encrypted and visible to the token holder (likely the payee) whereas the Payer Data is encrypted and visible only to the Payer's ILSP.

Both data sets define limits for the token, denominated in the asset and scale of the payee and payer accounts.

| Field | Description |
|-------|-------------|
| asset | The asset of the account. If a payer has multiple accounts that the ILSP could send from this provides guidance as to which asset should be spent when this token is redeemed by the payee. |
| scale | Provides the scale of the number used in `min` and `max` which are both expressed an unsigned 64-bit integers. |
| min   | In the Payee Data, this is the minimum amount that will be delivered. The ILSP will not attempt the payment if the current rate suggests this will not be possible. In the Payer Data, this is the minimum amount that must be sent per payment. This may be set by the payer in the case that there are fixed fees to send that make sending payments smaller than a certain size un-viable. Assumed to be 0 if not provided. |
| max   | In the Payee Data, this is the maximum amount that should be delivered. The ILSP will attempt to deliver no more than this amount. The payee may request less than this, in which case the ILSP should return a new token after a successful payment with this value reduced by the amount delivered. In the Payer Data, this is the maximum amount that must be delivered. This is the limit that the payer has defined for this token and the ILSP must not attempt to make a payment if the current rate suggests that this will need to be exceeded in order to deliver the `payee.minimum`.

## Flow

### Request

A payee or other system may request a new token and specify the parameters of the token that they require including the ILP Address to send to, asset of the payee account and max and min amounts to set in the Payee Data.

### Issuing

A token may be issued by either the payer or their ILSP on their behalf. The token is both signed (using a SHA-256 HMAC) and optionally contains encrypted data (encrypted using AES GCM and a 256-bit key) visible only to the payer (and possibly their ILSP).

An ILSP that processes tokens on behalf of a payer must keep a unique secret per payer (a `payer_secret`). A payer that generates and processes its own token MAY use a single `payer_secret`.

It is good practice to change this secret regularly and to always issue tokens with a limited lifetime (a value of `exp` that is not too far in the future). In that way the issuer can be confident about when it can retire an old secret after it has been replaced, and reject any tokens that claim to be signed using that old secret.

Whenever a new token is generated a new signing and encryption key should be derived for this token.

The ILSP should generate a unique identifier for the token, the `jti` (a 128-bit UUID is recommended) and derive the keys as follows:

```
token_seed = SHA-256(payer_secret || jti)
signing_key = SHA-256("signing_key" || token_seed)
encryption_key = SHA256("encryption_key" || token_seed)
```

Any restrictions required by the payer are defined in Payer Data which is encrypted into a JWE using the derived `encryption_key` as the CEK per the instructions in RFC7516. 

The value of the `alg` header must be `dir` and the value of the `enc` header must be `A256GCM` in the JWE Protected Header of this JWE. No other headers are allowed.

The 96-bit IV (the value of the ``) must be randomly generated.

The JWE, using the Flattened JWE JSON Serialization Syntax as described in [RFC7516 Section 7.2.2]((https://tools.ietf.org/html/rfc7516#section-7.2.2), is used as the value of the `payer` claim in the token.

Any restrictions specified by the payee are defined in the Payee Data which is set as the value of the `payee` claim.

The unique JWT identifier (used in the key generation process) is used for the value of the `jti` claim, the ILP Address of the payee as the value of the `sub` claim and an identifer of the payee is specified in the `iss` claim. If the token is generated by an ILSP (other than the payer) then the value of `iss` must uniquely identify the payer.

The `aud` claim must be an HTTPS URL where the payee is able to submit the token and request a payment.

If the token is to be time limited then either an `exp` or a `nbf` or both claims must be set. It is recommended that an `exp` value is always set and that issuers enforce a policy of keeping this window short to allow for old secrets to be retired.

The `iat` value should be set to the current time as this will assist in identifying the `sender_secret` that was used (in combination with the `iss` value) assuming the issuer regularly changes the `sender_secret`.

The token should then be signed using the `HMAC using SHA-256` algorithm as described in [RFC7515](https://tools.ietf.org/html/rfc7515) and serialized using the Flattened JWS JSON Serialization Syntax as defined in [RFC7515 Section 7.2.2](https://tools.ietf.org/html/rfc7515#section-7.2.2).

No unprotected headers are allowed.

### Redemption

A token is redeemed by submitting it to the endpoint defined in the `aud` value. An ILSP that is processing a token should reject it if the value of `aud` does not match the URL of the endpoint at which the token was submitted.

The token is redeemed by submitting it as an HTTP POST to the URL in the `sub` value of the claim. A `Pay-Token` header is also set by the payee and will be used to identify further requests to make payments authorized by this token.

```http
POST /ilp HTTP/1.1
Host: superwallet.example
Pay-Token: 7y0SfeN7lCuq0GFF5UsMYZofIjJ7LrvPvsePVWSv450

{
  "payload":"eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ",
  "protected":"eyJhbGciOiJFUzI1NiJ9",
  "signature":"DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
}
```

If the token is valid and can be redeemed by this host then the ILSP/payer responds with an HTTP 201 Accepted response and a `Pay-Balance` header indicating the amount that can still be sent using the provided `Pay-Token` (denominated in the destination currency and scale and based on the maximum send amount and current estimated rate).

The response may also contain a `Location` header indicating the URL that the payee must use to submit subsequent payment requests using the `Pay-Token`.

```http
HTTP/1.1 201 Accepted
Pay-Balance: 1000
Location: /pay
```

To request a payment the payee submits another HTTP POST using the same `Pay-Token` header. The payee also attaches a `Pay` header with the amount, ILP address and shared key to use for the payment. The body of the request is used by the payer/ILSP as the `data` in the first ILP packet that is sent.

The ILP Address in the `Pay` header must be a sub-address of the `sub` value of the Interledger Token.

```http
POST /pay HTTP/1.1
Host: superwallet.example
Pay-Token: 7y0SfeN7lCuq0GFF5UsMYZofIjJ7LrvPvsePVWSv450
Pay: interledger-psk2 example.payee123.tx567 SkTcFTZCBKgP6A6QOUVcwWCCgYIP4rJPHlIzreavHdU 10

<body>
```

The response, if the payment was successful, is an HTTP 200 Success. The `Pay-Balance` header reflects the new balance of the token that can still be redeemed. The response body is the `data`, if any, of the last ILP Fulfill packet returned.

```http
HTTP/1.1 200 Success
Pay-Balance: 9786

<body>
```
 
At any point, the payee can call DELETE on the payment endpoint to signal that it is done using the `Pay-Token`. 

```http
DELETE /pay HTTP/1.1
Host: superwallet.example
Pay-Token: 7y0SfeN7lCuq0GFF5UsMYZofIjJ7LrvPvsePVWSv450
```

This will return a new Interledger Token that can be redeemed for the amount in the last `Pay-Balance` header.

```http
HTTP/1.1 200 Success

{
  "payload":"eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ",
  "protected":"eyJhbGciOiJFUzI1NiJ9",
  "signature":"DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
}
```
