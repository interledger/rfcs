# Interledger Protocol Errors

This spec defines a standard error format and codes to be used when ILP payments are rejected.

Inspired by [HTTP Status Codes](https://tools.ietf.org/html/rfc2616#section-10), ILP errors are categorized based on the intended behavior of the caller when they get the given error.

## Error Propagation

ILP connectors MUST relay errors when they are notified of a transfer being rejected.

Connectors SHOULD NOT modify the error codes or messages except in the following way: connectors MAY append their ILP addresses, separated from the error message by a newline (`\n`), to assist with debugging/tracing.

## Data Format

ILP errors are UTF-8 encoded strings that are a maximum of 65535 bytes long. Error messages that are too long for a ledger to handle SHOULD be truncated to the first 65535 bytes.

Errors consist of a three character code, followed by a colon (`:`) and an arbitrary message set by the entity that raised the error. Transport and application layer protocols MAY define error messages that have special significance in their context.

```
<Error Code>: <Error Message>
<Relaying Connector ILP Address>
<Relaying Connector ILP Address>
...
```

## Error Codes

### S__ - Sender Error

Sender errors indicate that the payment is invalid and should not be retried unless the details are changed.

| Code | Name | Description |
|---|---|---|
| **S00** | **Bad Request** | Generic sender error. |
| **S01** | **Invalid Packet** | The ILP packet was syntactically invalid. |
| **S02** | **Unreachable** | There was no way to forward the payment, because the destination ILP address was wrong or unreachable. |
| **S03** | **Invalid Amount** | The amount is invalid, e.g. it contains more digits of precision than are available on the destination ledger or the amount is greater than the total amount of the given asset in existence. |
| **S04** | **Insufficient Destination Amount** | The amount was insufficient (e.g. you tried to pay a $100 invoice with $10). |
| **S05** | **Wrong Condition** | The receiver generated a different condition and cannot fulfill the payment. |
| **S06** | **Unexpected Payment** | The receiver was not expecting a payment like this (the memo and destination address don't make sense in that combination, for example if the receiver does not understand the transport protocol used) |
| **S07** | **Cannot Receive** | The receiver is unable to accept this payment due to a constraint, e.g. a limit was exceeded. |

**S08** - **S50** are reserved for future use.
**S51** - **S99** are for application-defined errors.

### T__ - Temporary Error

Temporary errors indicate a failure on the part of the receiver or an intermediary system that is unexpected or likely to be resolved soon. Senders SHOULD retry the same payment again, possibly after a short delay.

| Code | Name | Description |
|---|---|---|
| **T00** | **Internal Error** | Like HTTP 500. Something threw an exception, that's all we know. Try again later after we've had time to fix it. |
| **T01** | **Ledger Unreachable** | The connector was not able to reach the next ledger. Try again later. |
| **T02** | **Ledger Busy** | The ledger is rejecting requests due to overloading. Try again later. |
| **T03** | **Connector Busy** | The connector is rejecting requests due to overloading. Try again later. |
| **T04** | **Insufficient Liquidity** | The connector would like to fulfill your request, but it doesn't currently have enough money. Try again later. |

**T05** - **T50** are reserved for future use.
**T51** - **T99** are for application-defined errors.

### R__ - Relative Error

Relative errors indicate that the payment did not have enough of a margin in terms of money or time. However, it is impossible to tell whether the sender did not provide enough error margin or the path suddenly became too slow or illiquid. The sender MAY retry the payment with a larger safety margin.

| Code | Name | Description
|---|---|---|
| **R01** | **Transfer Timed Out** | The transfer timed out, i.e. the next party in the chain did not respond. This could be because you set your timeout too low or because something look longer than it should. Try again with a higher expiry. |
| **R02** | **Insufficient Source Amount** | Either you didn't send enough money or there wasn't enough liquidity. Try again with a higher sending amount. |
| **R03** | **Insufficient Timeout** | The connector could not forward the payment, because the timeout was too low to subtract its safety margin. Try again with a higher expiry. |

**R04** - **R50** are reserved for future use.
**R51** - **R99** are for application-defined errors.

