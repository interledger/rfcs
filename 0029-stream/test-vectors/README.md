# Stream Frame Test Vectors
In order to verify different implementations of the STREAM specification, we provide a series of test vectors in JSON format to compare expected vs actual ASN.1 OER encoding/decoding values.

## Valid Test Vectors
The file [StreamPacketFixtures.json](https://github.com/interledger/rfcs/tree/master/0029-stream/test-vectors/StreamPacketFixtures.json) contains a JSON array of elements representing Stream packets with embedded Stream Frame values. The JSON file also includes a corresponding Base64-encoded binary representation of the ASN.1 OER bytes for a given packet/frame combination.
 
 Tests should be written to validate that encoded Stream packets match the expected binary output in the JSON file. Conversely, tests should also be written to validate that decoded binary values match the values in the JSON test vector file.
   
 Each array element in the JSON file contains an object whose properties have the the following meanings:

| Field | Description |
|----:|:----|
| `name` | The name of the test vector. |
| `packet` | A JSON object containing Stream Packet information. |
| `buffer` | A string containing the Base64-encoded bytes that are expected when the Stream packet and frames are encoded according to the rules of [IL-RFC-29](https://github.com/interledger/rfcs/blob/master/0029-stream/0029-stream.md). |
| `packet.sequence` | The Stream packet's sequence number |
| `packet.packetType` | The type of Stream packet represented in the test vector. |
| `packet.amount` | The Stream packet amount represented in the test vector. |
| `packet.frames` | An array of Stream Frames contained in the packet. |
| `packet.frames.type` | The type of the Stream Frame. |
| `packet.frames.name` | The common name of the Stream Frame.|
| `packet.frames.*` | Each Stream Frame has its own particular fields. For example, the `ConnectionNewAddress` frame has a `sourceAddress` property, whereas other frames do not. The JSON file contains a sample value of each property available in a particular frame. | 

## Test Validations
Each implementation of STREAM should work across the test vectors defined above. The following is a link to the test coverage in various projects (please submit a PR to this file if you have an implementation not defined in this list):

| Project | Fixture | Test Class |
| ---:    | :---:   |      :---: |
| Java (Hyperledger Quilt) | [StreamPacketFixtures.json](https://github.com/hyperledger/quilt/tree/master/codecs-parent/codecs-stream/src/test/resources/StreamPacketFixtures.json) | [StreamPacketFixturesTest.java](https://github.com/hyperledger/quilt/tree/master/codecs-parent/codecs-stream/src/test/java/org/interledger/codecs/stream/StreamPacketFixturesTest.java) |
| Javascript (ilp-protocol-stream) | [packets.json](https://github.com/interledgerjs/ilp-protocol-stream/blob/master/test/fixtures/packets.json) | [packet.test.ts](https://github.com/interledgerjs/ilp-protocol-stream/blob/master/test/packet.test.ts) 
| Rust (interleder-rs) | TBD. | TBD. |
