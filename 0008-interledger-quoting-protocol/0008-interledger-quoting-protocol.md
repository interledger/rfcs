# Interledger Quoting Protocol (ILQP)

## Appendix A: ASN.1 Module

```
--<ASN1.PDU Quote.QuoteRequest, Quote.QuoteResponse>--

Quote DEFINITIONS AUTOMATIC TAGS ::= BEGIN

  QuoteRequest ::= SEQUENCE {
    version INTEGER (0..65535),
    addresses IlpAddressSet,
    sourceAmount IlpAmount OPTIONAL,
    destinationAmount IlpAmount OPTIONAL,
    -- How long the receiver needs to fulfill the payment (when using TTP/ATP)
    -- Defaults to 1.5 seconds
    destinationHoldDuration IlpHoldDuration DEFAULT 1500000
  }

  QuoteResponse ::= SEQUENCE {
    version INTEGER (0..65535),
    connectorAccount IlpAccountName,
    -- Address that this quote response relates to
    address IlpAddress,
    -- Source or destination amount, depending on whichever one was NOT
    -- provided in the request.
    requestedAmount IlpAmount,
    sourceHoldDuration IlpHoldDuration
  }

  IlpAddressSet ::= SEQUENCE OF IlpAddress

  IlpAddress ::= SEQUENCE OF OCTET STRING

  IlpAccountName ::= OCTET STRING

  IlpAmount ::= SEQUENCE {
    exponent INTEGER (-128..127),
    mantissa INTEGER
  }

  -- Length of hold in microseconds
  IlpHoldDuration ::= INTEGER (0..18446744073709551615)

  exampleQuoteRequest QuoteRequest ::= {
    version 0,
    addresses {
      { "bitcoin", "bitstamp", "abcledger" },
      { "usfed", "wf", "abcledger" }
    },
    destinationAmount {
      exponent 0,
      mantissa 10
    },
    destinationHoldDuration 20000000
  }

  exampleQuoteResponse QuoteResponse ::= {
    version 0,
    connectorAccount "connie",
    address { "bitcoin", "bitstamp", "abcledger" },
    requestedAmount {
      exponent -2,
      mantissa 821
    },
    sourceHoldDuration 26000000
  }

END
```
