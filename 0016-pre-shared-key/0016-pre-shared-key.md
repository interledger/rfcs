---
title: The Pre-Shared Key Transport Protocol (PSK)
draft: 4
---
# Pre-Shared Key Transport Protocol (PSK)

The Pre-Shared Key (PSK) protocol is an end-to-end transport protocol, used by the sender and receiver of an ILP payment to decide on a condition and fulfillment for a payment. By default, the protocol also encrypts any additional data sent along with the payment, using [AES-256-GCM](https://en.wikipedia.org/wiki/Galois/Counter_Mode). The full ILP payment is authenticated through an [HMAC-SHA-256](https://en.wikipedia.org/wiki/Hash-based_message_authentication_code) which is used to generate the fulfillment of a PSK payment. The entirety of the PSK data, including public headers, encrypted private headers, and encrypted private data, is encoded into an octet-stream that forms the data portion of the [ILP Packet](https://interledger.org/rfcs/0003-interledger-protocol/draft-4.html#specification). The PSK data is authenticated via AES-256-GCM in addition to the HMAC-SHA-256 which authenticates the full ILP payment.

Pseudocode for this protocol can be read [at the bottom of this spec](#pseudocode).

As the name suggests, PSK relies on a pre-shared secret key. In application-layer protocols like [SPSP](https://github.com/interledger/rfcs/blob/master/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md), the receiver generates the shared key and shares it with the sender over an end-to-end secure communication channel such as HTTPS. Alternatively, a [Diffie-Hellman key exchange](https://en.wikipedia.org/wiki/Diffie%E2%80%93Hellman_key_exchange) could be used directly to generate the shared secret key.

An advantage of PSK is that the pre-shared secret key only needs to be shared once. As long as both parties possess this key and are listening for transfers, they can send payments between one another.

A disadvantage of PSK is that it is repudiable. Although the sender does get cryptographic proof that the recipient received the payment, that proof cannot be used to convince 3rd parties that the sender did indeed send the funds, because the sender could have generated the fulfillment themselves. However, simple proof for the sender that the recipient got the funds is sufficient in many applications. The [Interledger Payment Request](https://github.com/interledger/rfcs/blob/master/0011-interledger-payment-request/0011-interledger-payment-request.md) transport protocol should be used instead in cases where non-repudiable proof is required.

## Importance of PSK in ensuring network health

When a sender or connector asks  the next connector to forward a payment to the receiver, they need to specify, among other things, the end-to-end data which may convince the receiver to fulfill the
condition, and the source amount which will reward that next connector.

PSK enables the safe delivery of the end-to-end data, which in turn allows the receiver to check whether the on-ledger destination amount is high enough.
If the on-ledger destination amount is too low, that means either the sender, or one of the connectors along the path, used a transfer amount that was too low (i.e., is effectively trying to steal
a little bit).

If the destination amount is too low, even if just by a few percent, the receiver should reject the payment. If this happens, the sender should retry the payment, using a different route.
This way, eventually, connectors that try to steal money will lose traffic, which is how the Interledger protocol stack ensures the network stays healthy.
It is PSK's end-to-end data transportation that makes this continuous price competition possible, so that is one of the main advantages of PSK.

The destination amount can either be public or secret. If the destination amount is public, each connector along the path can make sure they pay a fair but sufficient outgoing transfer amount.
For the destination ledger, there will be a 1:1 rate between the transfer amount and the destination amount in the payment packet. For previous hops, this rate will be determined by their liquidity
curve for the destination ledger. A rational connector will try to stay informed of the exact current liquidity curve for each destination ledger, so that they never overpay.
Even if the destination amount is public and can be viewed by all connectors along the path, PSK ensures that it cannot be altered along the path.

If the destination amount is secret, connectors have to guess how much they would need to pay to convince the rest of the hops along the path to get the payment fulfilled.
Presumably the destination amount would be not much lower than the maximum achievable destination amount, so it will not be possible to hide the destination amount from the connectors entirely.
Secret destination amounts are also not currently supported, but support for them may be added in the future.

## Flow

1. The pre-shared secret key is shared out of band.
2. The sender creates a 16-byte (128-bit) nonce with cryptographically-secure randomness.
3. The sender constructs the PSK data:
    1. The sender starts with the PSK status line: `PSK/1.0\n`
    2. The sender appends the [public headers](#public-headers) (including the nonce), followed by `\n\n`.
    3. If the public `Encryption` header starts with `aes-256-gcm`, then the remainder of the PSK data after the public headers (padded with [PKCS](https://en.wikipedia.org/wiki/Padding_(cryptography)#PKCS7)) will be encrypted using AES-256-GCM with the pre-shared secret key, using the nonce as the initialization vector. The 16-byte AES-256-GCM authentication tag is attached to the `Encryption` header, encoded in base64url. Note: The ciphertext is raw binary data, and is not base64 encoded. If the public `Encryption` header is set to `none`, then the remainder of the PSK data will be appended in unaltered cleartext.
    4. The sender appends the [private headers](#private-headers), followed by `\n\n`.
    5. The sender appends the application data (in its raw binary format).
4. The sender creates the condition of their payment by taking the HMAC of the full ILP packet with the pre-shared secret key, and computing the SHA-256 hash of it.
5. The sender quotes and sends their payment, setting the data field of the ILP packet to the PSK data.
6. The receiver gets notified by their ledger of an incoming prepared transfer with an ILP packet.
7. If the public `Encryption` header is set, then the receiver derives the payment encryption key from the pre-shared secret key, sets the AES-256-GCM initialization vector to the `Nonce` header in the PSK public headers, and uses them to decrypt the private headers and their data. The AES-256-GCM authentication tag is attached to the `Encryption` header. If the public `Encryption` header is set to `none`, the receiver parses the private headers and their data in clear-text.
8. The receiver verifies that the amount in the incoming transfer matches the amount in the ILP packet. The receiver may also call an external system to make sure the incoming funds are expected.
9. The receiver fulfills the incoming transfer with the HMAC of the ILP packet, using the same HMAC key as the sender, derived from the shared secret.

## Data Format

The PSK details are divided into two sets of headers. Each set of headers is formatted like those found in [HTTP Requests](https://tools.ietf.org/html/rfc7230#section-3.2) and follows the format `Header-Name: Header-Value`. Note that implementations have to validate inputs before using it as part of `Header-Name` or `Header-Value`. 

**PSK Headers MUST NOT contain any line feed characters such as `\n`**. Implementations failing to enforce this requirement may be vulnerable to [Header Injection Attacks](https://en.wikipedia.org/wiki/HTTP_header_injection).

Application data is appended to the private headers, after a blank line. This object is then encrypted and appended to the public headers as binary data, after a blank line. Both private and public headers are parsed in the exact same way as HTTP headers. All strings are UTF-8 encoded.

### Nonce

Every PSK payment must generate a random 16-byte (128-bit) nonce. A cryptographically secure source of randomness **MUST** be used.

The nonce is included in the PSK data, which is then put into the ILP packet and hashed to generate the payment's fulfillment. Because each PSK payment's fulfillment is an HMAC of its ILP packet and the shared secret, repeating the same ILP packet without a different nonce would yield a payment with the same fulfillment. A malicious connector could save up the fulfillments of PSK payments and then submit them whenever a packet is repeated exactly.

The nonce is also used to set the initialization vector of AES, ensuring that the same data will encrypt to different ciphertext across different payments. This is important to prevent connectors from figuring out the cleartext of the application data. If the nonce is repeated, then any payments containing that repeated nonce can be decrypted.

### Public Headers

The public headers and their data are formatted as below:

```http
PSK/1.0
Nonce: fpwpAhlN588
Key: hmac-sha-256
Encryption: aes-256-gcm 58EowcXBk3qBIvJ0kmvdCh
Header: data_everyone_can_see

...
```

The public headers come after a single status line, which must be `PSK/1.0`. Public headers are visible to all parties transmitting the packet, so they SHOULD contain only the bare minimum required for the intended parties to decrypt and validate the private headers.

PSK payments use an HMAC of the PSK details as a fulfillment, to prove that the contents are unmodified. The pre-shared secret key is the key used in the HMAC.

The data attached to these headers is an encrypted binary blob. This encrypted blob contains the private PSK headers.

Despite the fact that connectors can read the public headers' data, connectors should not be required to do so, nor should they rely on PSK details being present on all transfers. This information is only intended for the initial sender and final receiver of a payment.

The decryption key is derived from the pre-shared secret key, and the AES-256-GCM initialization vector is set to the value of the `Nonce` header (`fpwpAhlN588` in the above example). The nonce MUST be generated with cryptographically-secure randomness. **If the nonce is reused with the same shared secret, it could leak unencrypted data or allow money to be stolen by malicious parties.** The 16-byte AES-256-GCM authentication tag used for decryption is attached to the `Encryption` header, encoded in base64url (`58EowcXBk3qBIvJ0kmvdCh` in the above example). The encryption MUST use [PKCS](https://en.wikipedia.org/wiki/Padding_(cryptography)#PKCS7) for padding.

| Header | Value |
|--------|-------|
| `Nonce` | _(Required)_ A [base64url-encoded](https://en.wikipedia.org/wiki/Base64#URL_applications) nonce, used to generate ensure uniqueness of the PSK data and as an initialization vector (IV) for AES-256-GCM encryption. The nonce **MUST** be 16 bytes, and **MUST** be generated with cryptographically-secure randomness. |
| `Encryption` | _(Required)_ Supported values are `aes-256-gcm <AUTH_TAG>` and `none`. If it is set to `aes-256-gcm`, then private headers and application data will be AES-256-GCM encrypted, and `<AUTH_TAG>` will be the 16-byte authentication tag returned by the cipher, encoded in base64url. If it is set to `none`, then private headers and application data will be in cleartext. This cleartext will still be appended to the public headers after an empty line. If the value is neither `aes-256-gcm` nor `none`, the receiver MUST reject the incoming payment with an `S06: UnexpectedPayment` error. |
| `Key` | _(Optional)_ The algorithm by which the receiver generates the shared secret. In the normal use of PSK 1.0 described in this spec, the secret is generated by the receiver only and the sender does not know the algorithm used. In other cases, for example using [Diffie-Hellman](https://en.wikipedia.org/wiki/Diffie%E2%80%93Hellman_key_exchange), the sender would include the algorithm and a sender-specified key for the recipient to use to derive the shared secret. If the receiver does not understand the `Key` value, the receiver MUST reject the incoming payment with the error message `S06: UnexpectedPayment`. |
| ... | _(Optional)_ Additional headers. These can be read by any connectors. |

### Private Headers

The private headers and their data are formatted as below:

```http
Expires-At: 2017-03-13T16:58:06.901Z
Header-A: some_stuff
Header-B: some_other_stuff
Header-C: some_more_stuff
Date: 2017-03-13T16:57:56.901Z
Content-Type: application/json

{"foo":"bar"}
```

Only the payment's sender and receiver can decrypt and read the private headers and their data. The private headers contains an arbitrary message body preceded by the following headers:

| Header | Value |
|--------|-------|
| `Expires-At` | _(Optional)_ An [ISO8601 UTC timestamp](https://en.wikipedia.org/wiki/ISO_8601), after which this PSK payment has expired. |
| `Content-Type` | _(Optional)_ The [media type](http://www.iana.org/assignments/media-types/media-types.xhtml) of the data in the message body |
| ... | _(Optional)_ Additional arbitrary headers. Where appropriate, it is RECOMMENDED to match the headers defined for HTTP messages ([RFC7230](https://tools.ietf.org/html/rfc7230#section-3.2)) |

## Pseudocode

The following pseudocode outlines the generation procedure for the necessary values involved in PSK. It follows only the case where encryption is enabled, for simplicity.

### 1. Payment Creation

This is executed by the sender for each payment once they have the `shared_secret` and `destination_account` from the receiver:

```js
/**
  * @param shared_secret (sent by the receiver)
  * @param destination_account (sent by the receiver)
  *
  * @param headers (a list of HTTP style headers, which will be encrypted)
  * @param public_headers (a list of HTTP style headers, which will be left
  * unencrypted)
  * @param application_data (arbitrary binary data used for higher level
  * protocols, which will be encrypted)
  * @param destination_amount (amount that the receiver will receive on their
  * ledger, used to construct the ILP packet)
  */

// Private headers and application data are included first, separated by an empty line.

private_headers = create_empty_buffer()
private_headers += headers.join('\n')
private_headers += '\n\n'
private_headers += application_data

// A key is created in order to encrypt the private headers and the application
// data. A nonce is used to generate the key, so that the same private headers
// will not produce the same ciphertext. Also note that the nonce's inclusion
// in the ILP packet ensures that multiple payments using the same shared
// secret result in different hashes.

nonce = random_bytes(16)

// If you want to send data unencrypted, you can skip this encryption step and
// set the public 'Encryption' header to 'none' instead of 'aes-256-gcm'. The
// receiver side must always check the public 'Encryption' header to check
// whether or not encryption is enabled. This pseudocode only describes the
// case where encryption is turned on, for simplicity.  The nonce is used as
// the IV (initialization vector) of AES-256-GCM. The 16-byte auth tag of GCM
// will be attached to the 'encryption' header in base64url. The encrypted data
// should be automatically padded with PKCS.

payment_encryption_key = hmac_sha_256(shared_secret, 'ilp_psk_encryption')
encrypted_data, auth_tag = aes_256_gcm({
  key: payment_encryption_key,
  iv: nonce,
  data: private_headers
})

// The PSK data object is constructed from the public headers, encrypted private
// headers, and the encrypted application data. The nonce and the AES-256-GCM
// authentication tag are included in the public headers.

psk_data = create_empty_buffer()
psk_data += 'PSK/1.0\n'
psk_data += 'Nonce: ' + nonce
psk_data += 'Encryption: aes-256-gcm ' + auth_tag
psk_data += public_headers.join('\n')

// Encrypted private headers and application data are appended after an empty line.

psk_data += '\n\n'
psk_data += encrypted_data

// The ILP packet includes the destination account, amount and PSK data.

ilp_packet = create_ilp_packet({
  amount: destination_amount,
  account: destination_account,
  data: psk_data
})

// The sender generates the payment condition from the packet and shared
// secret, and uses it for their outgoing transfer. The receiver will perform
// this same derivation when fulfilling the payment. For the sender, the
// fulfillment is just an intermediate value in calculating the condition.

fulfillment_generator = hmac_sha_256(shared_secret, 'ilp_psk_condition')
fulfillment = hmac_sha_256(fulfillment_generator, ilp_packet)
condition = sha_256(fulfillment)

// The sender will now quote and prepare this payment with the condition
// and the ilp_packet attached.
```

### 2. Payment Fulfillment

This is executed by the receiver for each payment once they have gotten the notification of the incoming transfer:

```js
/**
  * @param shared_secret (same as the one used by the sender)
  * @param account (the receiver's account, as provided by their ledger plugin)
  * @param ilp_packet (the ILP packet attached to the incoming payment)
  */

// The nonce is taken from the public headers and used as the IV
// (initialization vector) of AES-256-GCM. The auth tag for GCM decryption is
// the second space-separated field of the 'encryption' header. Note that the
// header names are case-insensitive but the values are case-sensitive, just as
// in HTTP. If the public 'Encryption' header were set to 'none', this
// decryption function would be omitted, as packet.data would contain the
// plaintext of the private headers and application data.

psk_data = packet.data
nonce = psk_data.headers['nonce']
auth_tag = psk_data.headers['encryption'].split(' ')[1]
payment_decryption_key = hmac_sha_256(shared_secret, 'ilp_psk_encryption')
private_headers = aes_256_gcm_decipher({
  key: payment_decryption_key,
  iv: nonce,
  tag: auth_tag,
  data: psk_data.data
})

// After extracting and decrypting the PSK data, the receiver passes it to
// another function to perform any application-level logic on whether or not to
// accept this payment.

review_payment(private_headers, psk_data, ilp_packet, ... )

// Having reviewed the payment without exception, the receiver regenerates the
// fulfillment from the shared secret and the ILP packet, and then uses it to
// fulfill the incoming payment.

fulfillment_generator = hmac_sha_256(shared_secret, 'ilp_psk_condition')
fulfillment = hmac_sha_256(fulfillment_generator, ilp_packet)

// The receiver submits the fulfillment to execute the incoming transfer.
```

## Appendix A: Recommended Algorithm for Generating Shared Secrets

The receiver MAY use any method they choose for determining the `shared_secret`. This algorithm is RECOMMENDED because it allows the receiver to listen for incoming PSK payments with many different shared secrets without needing to store all of the various secret values.

The receiver maintains one `receiver_secret`, which is HMACed with a random public `token` to generate the shared secret initially and regenerate it from incoming payment packets.

### Shared Secret Generation

This is executed by the receiver, using a single `receiver_secret`, each time a new `shared_secret` is desired (NOT once per payment):

```js
/**
  * @param account (this is the address the receiver will listen on, as
  * returned by their ledger plugin)
  * @param receiver_secret (a random 32-byte secret generated and stored by the receiver)
  */

// The token is attached to the receiver's ILP address, allowing them to
// regenerate the shared secret every time they receive a payment, instead of
// keeping a store of all shared secrets they've given out.

token = random_bytes(16)

// The receiver id differentiates this receiver from other receivers on the
// same account with different receiver_secrets. When they receive a payment,
// the receiver can make sure the receiver id in the ILP address is their own.

receiver_id = hmac_sha_256(receiver_secret, "ilp_psk_receiver_id").slice(0, 8)
destination_account = account + "." + base64url(receiver_id) + base64url(token)

// The shared secret is generated using a hard-coded string and the token.

shared_secret_generator = hmac_sha_256(receiver_secret, "ilp_psk_generation")
shared_secret = hmac_sha_256(shared_secret_generator, token)

// The shared_secret and the destination_account are transmitted to the sender.
```

### Shared Secret Regeneration

This is executed each time a payment is received, before [2. Payment Fulfillment](#2-payment-fulfillment):

```js
/**
  * @param ilp_packet (the ILP packet attached to the incoming payment)
  * @param receiver_secret (same as generated above)
  * @param account (the receiver's account, as provided by their ledger plugin)
  */

// The receiver id and the shared secret are regenerated from the account in
// the ILP packet. Remember from the previous section that this address contains
// the token appended after the receiver id.

receiver_id = hmac_sha_256(receiver_secret, "ilp_psk_receiver_id").slice(0, 8)
token = ilp_packet.account.slice(account.length + receiver_id.length)
shared_secret_generator = hmac_sha_256(receiver_secret, "ilp_psk_generation")
shared_secret = hmac_sha_256(shared_secret_generator, token)

// Now the receiver can continue with Payment Fulfillment.
```
