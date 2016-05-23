# Interledger Quoting Protocol (ILQP)

## Appendix A: ASN.1 Module

```
--<ASN1.PDU Quote.QuoteRequest, Quote.QuoteResponse>--

Quote DEFINITIONS AUTOMATIC TAGS ::= BEGIN

  QuoteRequest ::= SEQUENCE {
    version INTEGER (0..65535),
    requestId IlpQuoteRequestId,
    ledgerId IlpLedgerId,
    directions IlpDirectionSet,
    amount IlpAmount,
    amountType IlpAmountType,
    additionalRoutingInfo IlpRoutingInfoSet OPTIONAL,
    -- Ten seconds seems like a good default :)
    destinationHoldDuration IlpHoldDuration DEFAULT 10000000
  }

  QuoteResponse ::= SEQUENCE {
    version INTEGER (0..65535),
    requestId IlpQuoteRequestId,
    connectorAccount IlpAccountName,
    -- Source or destination amount, depending on which one was not
    -- provided in the request.
    requestedAmount IlpAmount,
    sourceHoldDuration IlpHoldDuration
  }

  IlpQuoteRequestId ::= INTEGER (0..4294967295)

  -- Connector's local ID for that ledger
  IlpLedgerId ::= UTF8String

  IlpDirectionSet ::= SEQUENCE OF IlpDirection

  IlpDirection ::= UTF8String

  IlpAccountName ::= UTF8String

  IlpAmount ::= SEQUENCE {
    mantissa INTEGER,
    exponent INTEGER (-128..127)
  }

  IlpAmountType ::= ENUMERATED {
    fixedSource (0),
    fixedDestination (1)
  }

  IlpRoutingInfoSet ::= SEQUENCE OF IlpRoutingInfo

  IlpRoutingInfo ::= SEQUENCE {
    type INTEGER (0..65535),
    data OCTET STRING
  }

  -- Length of hold in microseconds
  IlpHoldDuration ::= INTEGER (0..18446744073709551615)

  exampleQuoteRequest QuoteRequest ::= {
    version 0,
    requestId 12345,
    ledgerId "rippleXRP",
    directions {
      "bitcoin/bitstamp/abcledger",
      "usfed/wf/abcledger"
    },
    amount {
      mantissa 10,
      exponent 0
    },
    amountType fixedSource,
    destinationHoldDuration 20000000
  }

  exampleQuoteResponse QuoteResponse ::= {
    version 0,
    requestId 12345,
    connectorAccount "connie",
    requestedAmount {
      mantissa 821,
      exponent -2
    },
    sourceHoldDuration 26000000
  }

END
```
