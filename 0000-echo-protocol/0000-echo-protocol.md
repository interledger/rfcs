# Echo Protocol

## Introduction

In order to monitor the health of an internetworked system, it is often useful to be able to send test messages. However, not every participant of the system will have multiple points of access to test between or, if they do, they may want to test additional routes.

In the Internet system, a mechanism is provided for sending a message to an arbitary host and receiving a response back. This mechanism is coloquially known as a "ping" and allows users to test their connectivity against countless Internet hosts. We would like to provide a similar mechanism for Interledger.

## Scope

It is already possible to test end-to-end connectivity in Interledger using the quoting mechanism. By requesting a quote, we can check if there is theoretically liquidity between our own account and the destination account. However, this does not prove the liquidity is actually available and it does not say anything about the availability of liquidity in the opposite direction. The Interledger Echo Protocol is designed to be able to fully exercise liquidity in both directions.

The echo protocol is designed to test uptime, latency and cost. It is not designed to debug routing issues and does not provide additional diagnostic information about the state of routing. That use case would be better served by a separate traceroute mechanism.

All Interledger implementations should implement the echo service, unless they have a specific reason not to, such as security or privacy concerns.

## Terminology

* The **Client** is the Interledger implementation initiating the echo request.
* The **Mirror** is the Interledger implementation responding to the echo request.
* **Source amount** is the amount debited from the sender of an ILP payment.
* **Destination amount** is the amount credited to the recipient of an ILP payment.

## Protocol

1. The Client requests a quote by source amount using the following details:
  - Source amount: A small amount considered (by the Client) to be sufficient for a round trip
  - Destination ILP address: Mirror's ILP address
2. Upon receiving a quote response, the Client sends a payment using the following details:
  - Source amount: The same source amount as in step 1
  - Destination amount: The quoted destination amount from the quote response
  - Destination ILP address: Mirror's ILP address
  - Data: The string `PING` followed by a newline character (a 0x0A byte), followed by a UUID in canonical textual representation, followed by another newline character, followed by the Client's ILP address.

    Example:
    ```
    PING
    0c009642-f64c-45c7-b9e8-a57c95a60556
    example.myledger.test
    ```
3. Upon receiving the prepared transfer, the Mirror initiates a payment using the following details:
  - Source amount: Same as the incoming destination amount
  - Destination amount: 0
  - Destination ILP address: Client's ILP address (taken from the data field of the incoming payment)
  - Data: The string `PONG` followed by a newline character (a 0x0A byte), followed by the UUID taken from the incoming payment's data field.

    Example:
    ```
    PONG
    0c009642-f64c-45c7-b9e8-a57c95a60556
    ```
4. Upon receiving the prepared transfer, the Client fulfills it. From here, the payment completes normally.

If an error occurs between steps 3 and 4, the Mirror should relay the error by rejecting the incoming transfer the same way a connector would when relaying an error.

## Recommended Uses

Participants of the Interledger network may use this mechanism to test their own connectivity by sending pings to one or more destinations that are known to support the protocol described in this document.

A monitoring service that is testing the availability of different ILP connectors may send pings to these connectors from various sources. Connectors that wish to use this monitoring service must support the protocol described in this document.
