# Bluetooth Payment Protocol

This document specifies a protocol for communicating and authorizing Interledger Payment Requests over Bluetooth (Low Energy). It is primarily intended for use in in-person retail payment contexts.

This protocol may be implemented on Customer devices such as smartphones or very low-power offline devices as our example[tapFi](https://github.com/joaopedrovbs/tapFi).

Once a Customer becomes active by broadcasting it's payment service over BLE, Merchants can connect
and request signature for payments over a secure Bluetooth channel. The channel is closed once
a payment is signed or the Customer cancels the purshase for security or authentication reasons.

## Definitions

- `IPR`: [Interledger Payment Request](../0011-interledger-payment-request/0011-interledger-payment-request.md)
- `Merchant`: The one requesting a payment
- `Customer`: The one authorizing and remitting payment
- `Connection`: Short time binding between `Merchant` and `Customer`
- `ILP Account`: An account on a Interledger-enabled ledger
- `ILP Address`: [Interledger](../0015-ilp-addresses/0015-ilp-addresses.md) address in the form of `g.us.somebank.youraccount`
- `Merchant Certificate Authority`: Like CA's for TLS certificates, Merchant CAs sign the certificates of trusted merchants. CAs MUST maintain blacklists of compromised keys
- `Redemption URI`: URI where the Merchant can submit Customer-authorized IPRs to initiate an ILP payment to their account (Note: the service that implements this MUST store previously redeemed IPRs to avoid duplicate payments)
- `Write Long Characteristic`: GATT Sub-Procedure that Writes to Characteristics with more than 20 bytes


## GATT Services: BLE Description
> Generic Attribute Profile (GATT) is how information is transmited between connected BLE devices, by
exposing Services that contains Characteristics. Each Characteristic works like a single "register".

#### ILP Account Information
> Service that provides identity of the Customer

**Characteristics:**

- `name`: (Read)


#### ILP Payment Request

> Service that enables Merchant to issue payment requests to Customer

*Characteristics:*

- `:status`: (Read | Notify)
  - __waiting__: Initial state. Always reset on new connection.
  - __invalid__: Payment failed because the IPR did not pass validation by the Customer's device.
  - __authenticating__: IPR has passed the Customer device's validation and is now waiting for user authorization.
  - __unauthenticated__: Payment was canceled because of invalid password
  - __canceled__: Payment was canceled by the Customer. 
  - __complete__: Payment complete. Read `:iprAuthorization` for the signed packet
- `:action` (Write)
  - __sign__: Initiate signing after `:packet`, `:packetSignature`, `:merchantPublicKey` and `:merchantCertificate` have been written.
- `:ipr`: (Write Long Characteristic)
  - ILP Packet containing destination Address and Cost
- `:iprSignature`: (Write Long Characteristic)
  - Merchant signature on IPR.
- `:merchantPublicKey`: (Write Long Characteristic)
- `:merchantCertificate`: (Write Long Characteristic)
- `:iprAuthorization`: (Read Long Characteristic)
  - Device signature on IPR

## Merchant Setup

1. Merchant generates certificate with Ed25519 public key
2. Merchant submits certificate, ILP account address, and per-payment limit to a Merchant Certificate Authority
3. Certificate Authority signs merchant details

## Customer Device Setup

1. Device manufacturer embeds unique Ed25519 public / private key pair in device. The manufacturer MUST ensure the device is tamper-proof.
2. Device manufacturer signs the device public key with their own key pair.
3. Customer submits the device public key and manufacturer's signature to their ledger operator to authorize the device to spend funds from their account.
4. If the device manufacturer is trusted to produce secure devices, the ledger operator signs the device public key and a per-payment spending limit with their own key.
5. Customer stores the ledger operator's signature, certificate, per-payment and total spending limit on the device (**TODO**: would it make more sense to have the manufacturer include the ledger signature and cert in the device?).

### Payment Flow

**[MERC]** indicates steps taken by the Merchant

**[CUST]** indicates steps taken by the Customer's device

1. **[MERC]** Listen to Broadcasts of the [ILP Account Information](#ILPAccountInformation). List customers.
2. **[MERC]** Select customer for payment, and initiate a connection over BLE.
3. **[MERC]** Generate IPR with __account__ and __amount__.
4. **[MERC]** Sign the IPR using their Ed25519 keypair
5. **[MERC]** Write to:
  1. `:ipr` with IPR
  2. `:iprSignature` with Signature of IPR
  3. `:merchantPublicKey` with the Merchant Public Key 
  4. `:merchantCertificate` with the Certificate signed by a Certificate Authority
6. **[MERC]** Write __sign__ to `:action`, to indicate data is ready to be validated/signed.
7. **[MERC]** Listen to notifications on `:status`
8. **[CUST]**  Write __"authenticating"__ to `:status`
9. **[CUST]** Validates payload on Characteristics. If:
  1. [CA is NOT trusted:](#) write __"invalid"__ to `:status`. Close connection
  2. [Payment NOT within limits:](#) write __"invalid"__ to `:status`. Close connection
  3. [Certificate NOT valid for ILP address in IPR:](#) write __"invalid"__ to `:status`. Close connection
  4. [Merchant signature is NOT on IPR:](#) write __"invalid"__ to `:status`. Close connection
  5.  (**TODO**: what if the device is super simple and low-power, like a tapFi, and can't easily verify a chain of signatures? Is there any way to make it safe to skip this step?).
10. **[CUST]**  Wait for Customer authorization (passkey/rhythm/Harry Potter wand...). If:
  1. [Password is NOT valid:](#) write __"unauthenticated"__ to `:status`. Close connection.
  2. [Authentication timeout:](#) write __"unauthenticated"__ to `:status`. Close connection.
  3. [If payment is canceled:](#) write __"canceled"__ to `:status`. Close connection.
11. **[CUST]** Sign IPR using its ED25519 keypair
  1. (**TODO**: should it include the merchant cert and/or signature on the IPR in the data being signed?)
12. **[CUST]** Writes to:
  1. `:iprAuthorization` with signed IPR, Redemption URI, public key (**TODO**: can the pubkey be recovered from the signature?) and certificate signed by the customer's ledger (and possibly another CA) to the merchant
  2. (Should we send the keys before signing? Sending this thing depends on if the merchant is online or not. I think It should be separated into read-only characteristics)
13. **[CUST]** Write __"complete"__ to `:status`. Close connection.
14. **[MERC]** Once notified on `:status` with __"complete"__, If:
  1. [Online:](#) Merchant submits signed IPR, merchant certificate to the customer's submission endpoint. 
  2. [Offline:](#) Merchant MAY accept the signed request as payment, taking the risk that the customer's ledger may not honor the signed request later.