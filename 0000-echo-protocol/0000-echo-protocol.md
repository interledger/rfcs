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

1. The Client sends a quote request with a destination ILP address of `[mirror's ilp address].echo.[client's ilp address]` and a destination amount of `0`. If the combined address is too long, the client aborts with an error.
2. Upon receiving the quote request, the Mirror initiates a quote request of their own for the Client's ILP address with an amount of `0`.
3. Upon receiving the quote response, the Mirror responds to the Client's quote request as if its destination amount had been the source amount of the quote response from step 2.
4. Upon receiving the quote response, the Client sends a payment using the quoted amount from step 3 and the same destination ILP address and amount as in step 1. The condition for the payment is the hash of a random nonce. The memo for the payment is the string "ECHO" followed by a space character (" "), followed by a UUID, encoded as an ASCII string.
5. Upon receiving the prepared transfer, the Mirror initiates a payment to the Client's ILP address with an amount of `0` using the incoming destination amount as the outgoing source amount.
6. Upon receiving the prepared transfer, the Client fulfills it. From here, the payment completes normally.

If a Client wishes to query the bidirectional liquidity without making a payment, it may stop before step 4.

If an error occurs between steps 5 and 6, the Mirror relays the error to the client, the same way a connector would relay an error.

## Recommended Uses

Participants of the Interledger network may use this mechanism to test their own connectivity by sending pings to one or more destinations that are known to support the protocol described in this document.

A monitoring service that is testing the availability of different ILP connectors may send pings to these connectors from various sources. Connectors that wish to use this monitoring service must support the protocol described in this document.
