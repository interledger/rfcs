# Interactive Transport Protocol (ITP)

## Preface

This document specifies the Interactive Transport Protocol. It is a host-to-host protocol for Interledger payment requests, which include receiver-generated conditions. This condition protocol enables receivers to verify that an incoming transfer matches a payment request previously created by them, without the receiver needing to keep a record of all outstanding payment requests.

## Introduction

### Motivation

The "Universal" mode of the Interledger Protocol uses holds based on Crypto Conditions and expiries to ensure a sender's funds are delivered to the destination or returned to the sender's account. (For more on the Interledger Protocol see [IL-RFC-3](../0003-interledger-protocol).)

A common approach is for conditions to be generated and fulfilled by the receivers of Interledger transfers. This document specifies one such approach that enables receivers to verify that an incoming transfer matches a payment request previously created by the receiver, without the receiver needing to keep a record of all outstanding payment requests.

### Scope

This document defines one approach for receiver-generated conditions. Since the condition is opaque to all parties aside from the receiver, the receiver may use any condition they choose. However, this specification includes best practices that receivers SHOULD take into consideration.

Communicating payment requests from the receiver to the sender is *not* included in this protocol and is to be handled by higher level protocols.

### Interfaces

This protocol is used by higher-level protocols for the receiver to generate conditions and payment requests. The sender MAY modify or add to the request details but the payment request SHOULD serve as an Interledger packet without modification.

### Operation

The receiver creates an Interledger Packet from the details of the payment they want to request from the sender. The receiver uses a secret to create an HMAC of the packet. This HMAC is used as the condition fulfillment. The condition is the hash digest of the HMAC output.

## Overview

### Relation to Other Protocols

     ------    
    | SPSP |
     ------ 
       |
     ------     -------
    | ITP  |   |   ?   |
     ------     -------
       |           |
     ------------------  
    |       ILP        |
     ------------------

The [Simple Payment Setup Protocol (SPSP)](../0009-simple-payment-setup-protocol) uses the Interactive Transport Protocol (ITP). ITP is a host-to-host protocol intended for use on top of the Interledger Protocol.

### Model of Operation

We suppose that a sender wants to pay a receiver for some good or service and that the two are using a communication channel specified by a higher level protocol.

We suppose that the receiver has a 32-byte secret value.

1. The receiver creates an Interledger Packet using the details of the payment they want to request from the sender. The `condition` field is left undefined.
2. The receiver creates the ITP Header (specified [below](#specification)) using a [UUID (version 4 is RECOMMENDED)](https://www.ietf.org/rfc/rfc4122.txt) and a token or string associated with the sender and/or good being purchased.
3. The receiver attaches the ITP header to the Interledger Packet.
4. The receiver encodes the complete Interledger Packet in the [Canonical OER](http://www.oss.com/asn1/resources/books-whitepapers-pubs/Overview%20of%20OER.pdf) format.
5. The receiver creates an [HMAC](https://tools.ietf.org/html/rfc2104) of the encoded packet using the SHA-256 hash function and the receiver's secret as the HMAC key.
6. The receiver uses the HMAC output as the _preimage_ for a [PREIMAGE-SHA-256 Crypto Condition](../0002-crypto-conditions) (the HMAC output is hashed again using SHA-256 to create the condition).
7. The receiver uses this condition as the `condition` field in the Interledger Packet.
8. The receiver communicates the complete Interledger Packet to the sender using the communication channel.
9. The sender requests a quote for the payment from a connector to the destination ILP address provided in the ILP packet and with a fixed destination amount corresponding to the amount given in the ILP packet.
10. The sender sends a transfer to a connector with the packet from the recipient attached.
11. Connectors forward the packet until it reaches the receiver's ledger and the receiver is notified of funds on hold.
12. The receiver checks the transfer against the packet details. The receiver checks that the transfer amount is greater than or equal to the amount specified in the packet, that the packet is not yet expired, and that the packet condition matches the transfer condition. If any of the checks fail, the receiver rejects the transfer or lets the hold expire and skips all further steps.
13. The receiver **regenerates** the condition fulfillment, following steps 4-6.
14. The receiver checks that the condition generated matches the one included in the incoming transfer. If it does not, the receiver rejects the transfer or lets the hold expire and skips all further steps.
15. The receiver submits the condition fulfillment to their ledger to claim the funds.
16. When the receiver's ledger confirms that the fulfillment has been received and the funds transferred, the receiver uses the `requestUniqueId` and the `receiverRequestPurpose` fields from the ITP Header to reconcile the incoming transfer with the original payment request (and take whatever action corresponds to the payment request being paid).

## Specification

### Interactive Transport Protocol Header

| Field | Type | Short Description |
|:--|:--|:--|
| version | INTEGER(0..255) | ITP protocol version (currently `1`) |
| requestUniqueId | ItpId | Unique ID for the request |
| receiverRequestPurpose | ItpRequestPurpose | Additional identifying information for the receiver to associate the incoming transfer |
| allowSenderData | Boolean | If true, do not include the `data` field in the hashed values |

#### version 

    INTEGER(0..255)

The version of the Interactive Transport Protocol being used. This document describes version `1`.

#### requestUniqueId

    IlpId :== OCTET STRING

A unique ID for the payment request. This MUST be unique to ensure that two payment requests do not have the same condition. It is RECOMMENDED to use a UUID.

#### receiverRequestPurpose

    ItpRequestPurpose :== OCTET STRING

The receiver may optionally include some additional identifying information to help them associate the transfer with its purpose when it arrives. For example, if a receiver is expecting multiple transfers from multiple senders, the receiver could store a sender ID or token (in addition to the `uniqueId`, which differs per request).

#### allowSenderData

    BOOLEAN

If true, allow senders to put data in the `data` field of the Interledger Packet and do not include the `data` field in hash for the condition.
