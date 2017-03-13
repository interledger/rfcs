# Pre-Shared Key

The Pre-Shared Key (PSK) protocol is an end-to-end transport protocol, used by the sender and receiver of an ILP payment to decide on a condition and fulfillment for a payment. By default, the protocol also encrypts any additional data sent along with the payment, using [AES-256-CTR](https://en.wikipedia.org/wiki/Advanced_Encryption_Standard). The PSK data is authenticated through an [HMAC-SHA-256](https://en.wikipedia.org/wiki/Hash-based_message_authentication_code) which is used to generate the fulfillment of a PSK payment. The entirety of the PSK data, including public headesrs, encrypted private headers, and encrypted private data, is expected to be encoded into an octet-stream that forms the data portion of the [ILP Packet](https://github.com/interledger/rfcs/blob/master/0003-interledger-protocol/0003-interledger-protocol.md).

Pseudocode for this protocol can be read [at the bottom of this spec](#pseudocode).

As the name suggests, PSK relies on a pre-shared secret key. In application-layer protocols like [SPSP](https://github.com/interledger/rfcs/blob/master/0009-simple-payment-setup-protocol/0009-simple-payment-setup-protocol.md), the receiver generates the shared key and shares it with the sender over an end-to-end secure communication channel such as HTTPS. Alternatively, a [Diffie-Hellman key exchange](https://en.wikipedia.org/wiki/Diffie%E2%80%93Hellman_key_exchange) could be used directly to generate the shared secret key.

An advantage of PSK is that the pre-shared secret key only needs to be shared once. As long as both parties possess this key and are listening for transfers, they can send payments between one another.

A disadvantage of PSK is that it is repudiable. Knowledge of a payment's fulfillment cannot be used as cryptographic proof that the receiver completed the payment, because both sender and receiver know how to generate the fulfillment with their pre-shared secret key. This causes no issues unless you have some other framework on top of ILP that relies on this cryptographic proof.

## Flow

1. The pre-shared secret key is shared out of band.
2. The sender creates a 16-byte (128-bit) nonce with cryptographically-secure randomness.
3. The sender constructs the PSK data:
    1. The sender starts with the PSK status line: `PSK/1.0\n`
    2. The sender appends the [public headers](#public-headers) (including the nonce), followed by `\n\n`.
    3. If the public `Encryption` header is set to `aes-256-ctr`, then the remainder of the PSK data after this point will be encrypted using AES-256-CTR with the pre-shared secret key, using the nonce as the initialization vector. Note: The ciphertext is raw binary data, and is not base64 encoded. If the public `Encryption` header is set to `none`, then the remainder of the PSK data will be appended in unaltered cleartext.
    4. The sender appends the [private headers](#private-headers), followed by `\n\n`.
    5. The sender appends the application data (in its raw binary format).
4. The sender creates the condition of their payment by taking the HMAC of the full ILP packet with the pre-shared secret key, and computing the SHA-256 hash of it.
5. The sender quotes and sends their payment, setting the data field of the ILP packet to the PSK data.
6. The receiver gets notified by their ledger of an incoming prepared transfer with an ILP packet.
7. If the public `Encryption` header is set, then the receiver derives the payment encryption key from the pre-shared secret key, sets the AES-256-CTR initialization vector to the `Nonce` header in the PSK public headers, and uses them to decrypt the private headers and their data. If the public `Encryption` header is set to `none`, the receiver parses the private headers and their data in clear-text.
8. The receiver verifies that the amount in the incoming transfer matches the amount in the ILP packet. The receiver may also call an external system to make sure the incoming funds are expected.
9. The receiver fulfills the incoming transfer with the HMAC of the ILP packet, using the same HMAC key as the sender, derived from the shared secret.

## Data Format

The PSK details are divided into two sets of headers. Each set of headers is formatted like those found in [HTTP Requests](https://tools.ietf.org/html/rfc7230#section-3.2). Application data is appended to the private headers, after a blank line. This object is then encrypted and appended to the public headers as binary data, after a blank line. Both private and public headers are parsed in the exact same way as HTTP headers.

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
Encryption: aes-256-ctr
Header: data_everyone_can_see

...
```

The public headers come after a single status line, which must be `PSK/1.0`. Public headers are visible to all parties transmitting the packet, so they SHOULD contain only the bare minimum required for the intended parties to decrypt and validate the private headers.

PSK payments use an HMAC of the PSK details as a fulfillment, to prove that the contents are unmodified. The pre-shared secret key is the key used in the HMAC.

The data attached to these headers is an encrypted binary blob. This encrypted blob contains the private PSK headers.

Despite the fact that connectors can read the public headers' data, connectors should not be required to do so, nor should they rely on PSK details being present on all transfers. This information is only intended for the initial sender and final receiver of a payment.

The decryption key is derived from the pre-shared secret key, and the AES-256-CTR initialization vector is set to the value of the `Nonce` header (`fpwpAhlN588` in the above example). The nonce MUST be generated with cryptographically-secure randomness. **If the nonce is reused with the same shared secret, it could leak unencrypted data or allow money to be stolen by malicious parties.**

| Header | Value |
|--------|-------|
| `Nonce` | _(Required)_ A [base64url-encoded](https://en.wikipedia.org/wiki/Base64#URL_applications) nonce, used to generate ensure uniqueness of the PSK data and as an initialization vector (IV) for AES-256-CTR encryption. The nonce **MUST** be 16 bytes, and **MUST** be generated with cryptographically-secure randomness. |
| `Encryption` | _(Required)_ Supported values are `aes-256-ctr` and `none`. If it is set to `aes-256-ctr`, then private headers and application data will be AES-256-CTR encrypted. If it is set to `none`, then private headers and application data will be in cleartext. This cleartext will still be appended to the public headers after an empty line. If the value is neither `aes-256-ctr` nor `none`, the receiver MUST reject the incoming payment with an "S??" (error code to be determined) error. |
| `Key` | _(Optional)_ The algorithm by which the receiver generates the shared secret. If this value is set to anything but `hmac-sha-256`, the receiver MUST reject the incoming payment with an "S??" (error code to be determined) error. |
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

### Receiver: Setup of the Protocol

This pattern of generating the shared secret based on a random token is not part of the PSK protocol, but allows a receiver to listen for incoming PSK payments with many different shared secrets. If the derivation of the shared secret in this first section is changed, then the [final section](#receiver-receipt-of-each-payment) must be changed to use the same shared secret.

```js
/**
  * @param account (this is the address the receiver will listen on, as
  * returned by their ledger plugin)
  */ 

// The token is attached to the receiver's ILP address, allowing them to
// regenerate the shared secret every time they receive a payment, instead of
// keeping a store of all shared secrets they've given out.

receiver_secret = random_bytes(32)
token = random_bytes(16)

// The receiver id differentiates this receiver from other receivers on the
// same account with different receiver_secrets. When they receive a payment,
// the receiver can make sure the receiver id in the ILP address is their own.

receiver_id = hmac_sha_256(receiver_secret, "ilp_psk_receiver_id").slice(0, 8)
receiver_address = account + "." + base64url(receiver_id) + base64url(token)

// This pattern of taking the HMAC of a secret and a hard-coded string will be
// repeated for the generation of many variables. It helps secure the secrets
// against any interactions between the algorithms used. This method of
// generating the shared secret is just a recommendation, but the receiver MUST
// be able to access or regenerate the shared secret in order to fulfill
// incoming payments.

shared_secret_generator = hmac_sha_256(receiver_secret, "ilp_psk_generation")
shared_secret = hmac_sha_256(shared_secret_generator, token)

// Now the shared_secret and the receiver_address are transmitted to the
// sender.
```

### Sender: Generation of Each Payment

```js
/** 
  * @param shared_secret (sent by the receiver)
  * @param receiver_address (sent by the receiver)
  *
  * @param headers (a list of HTTP style headers, which will be encrypted)
  * @param public_headers (a list of HTTP style headers, which will be left
  * unencrypted)
  * @param application_data (arbitrary binary data used for higher level
  * protocols, which will be encrypted)
  * @param destination_amount (amount that the receiver will receive on their
  * ledger, used to construct the ILP packet)
  */

// The private headers are put together first. Application data is attached to
// the private headers, after an empty line.

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
// set the public 'Encryption' header to 'none' instead of 'aes-256-ctr'. The
// receiver side must always check the public 'Encryption' header to check
// whether or not encryption is enabled. This pseudocode only describes the
// case where encryption is turned on, for simplicity.
// The nonce is used as the IV (initialization vector) of AES-256-CTR.

payment_encryption_key = hmac_sha_256(shared_secret, 'ilp_psk_encryption')
encrypted_data = aes_256_ctr({
  key: payment_encryption_key,
  iv: nonce,
  data: private_headers
})

// Now the PSK data object is constructed, containing the public headers, the
// encrypted private headers, and the encrypted application data. The
// "public_headers" are added, including a "key" header that specifies the
// HMAC algorithm used (which MUST be hmac-sha-256) and the nonce used to
// generate the payment's encryption key.

psk_data = create_empty_buffer()
psk_data += 'PSK/1.0\n'
psk_data += 'Nonce: ' + nonce
psk_data += 'Encryption: aes-256-ctr'
psk_data += 'Key: hmac-sha-256'
psk_data += public_headers.join('\n')

// The encrypted private headers and application data are appended after an
// empty line.

psk_data += '\n\n'
psk_data += encrypted_data

// An ILP packet is generated from the receiver's address and the amount that
// the sender wants to reach the receiver. The PSK data makes up the data field
// of the ILP packet.

ilp_packet = create_ilp_packet({
  amount: destination_amount,
  account: receiver_address,
  data: psk_data
})

// The sender generates the payment condition from the packet and shared
// secret, and uses it for their outgoing transfer. The receiver will perform
// this same derivation when fulfilling the payment. For the sender, the
// fulfillment is just an intermediate value in calculating the condition.

fulfillment_generator = hmac_sha_256(shared_secret, 'ilp_psk_condition')
fulfillment = hmac_sha_256(fulfillment_generator, ilp_packet)
condition = sha_256(fulfillment)

// The sender will now quote this payment and send it to the first connector,
// using the ilp_packet and the condition.
```

### Receiver: Receipt of Each Payment

```js
/** 
  * @param ilp_packet (the ILP packet attached to the incoming payment)
  * @param receiver_secret (same receiver_secret generated in the first section)
  * @param account (the receiver's account, as provided by their ledger plugin)
  */

// The receiver id and the shared secret are regenerated from the account in
// the ILP packet. Remember from the first section that this address contains
// the token appended after the receiver id.

receiver_id = hmac_sha_256(receiver_secret, "ilp_psk_receiver_id").slice(0, 8)
token = ilp_packet.account.slice(account.length + receiver_id.length)
shared_secret_generator = hmac_sha_256(receiver_secret, "ilp_psk_generation")
shared_secret = hmac_sha_256(shared_secret_generator, token)

// The nonce is taken from the public headers and used as the IV
// (initialization vector) of AES-256-CTR. Note that the header names are
// case-insensitive but the values are case-sensitive, just as in HTTP.  If the
// public 'Encryption' header were set to 'none', this decryption function
// would be omitted, as packet.data would contain the plaintext of the private
// headers and application data.

psk_data = packet.data
nonce = psk_data.headers['nonce']
payment_decryption_key = hmac_sha_256(shared_secret, 'ilp_psk_encryption')
private_headers = aes_256_ctr_decipher({
  key: payment_decryption_key,
  iv: nonce,
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
```
