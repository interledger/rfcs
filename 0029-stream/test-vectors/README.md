# Stream Frame Test Vectors
In order to verify different implementations of the STREAM specification, we provide a series of test vectors in JSON format to compare expected vs actual ASN.1 OER encoding/decoding values.

## Valid Test Vectors
The file [ValidStreamFrameTestVectors.json](https://github.com/interledger/rfcs/tree/master/0029-stream/test-vectors/ValidStreamFrameTestVectors.json) contains a JSON array of elements representing Stream Frame values in addition to a corresponding Base64-encoded binary reprsentation of the ASN.1 OER bytes for a given frame.
 
 Tests should be written to validate that encoded Stream frames match the expected binary output in the JSON file. Conversely, tests should also be written to validate that decoded binary values match the values in the JSON test vector file.
   
 Each array element in the JSON file contains an object whose values have the the following meanings:

* `type`: The type of the Stream Frame, as defined in [IL-RFC-29](https://github.com/interledger/rfcs/blob/master/0029-stream/0029-stream.md).
* `expectedAsn1OerBytes`: A string containing the Base64-encoded bytes that are expected when the specified Stream Frame is encoded into its ASN.1 OER encoding.
* `Misc Fields`: Each Stream Frame has its own particular fields. For example, the `ConnectionNewAddress` frame has a `sourceAddress` property, whereas other frames do not. The JSON file contains a sample value of each property available in a particular frame.

## Test Validations
Each implementation of STREAM should work across the test vectors defined above. The following is a link to the test coverage in various projects (please submit a PR to this file if you have an implementation not defined in this list):

* Java Stream: [ValidStreamFrameVectorsTest](https://github.com/hyperledger/quilt/blob/master/codecs-parent/codecs-stream/src/test/java/org/interledger/codecs/stream/frame/ValidStreamFrameVectorsTest.java)
* Rust Stream: TBD.
* Javascript Stream: TBD.
