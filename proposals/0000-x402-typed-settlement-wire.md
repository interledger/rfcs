---
title: The X402 Typed Settlement Wire Protocol over Interledger
type: proposal
draft: 1
author: Abdul Shabazz (veritasvaultone@gmail.com)
organization: Synaptics Lab
created: 2026-09-26
related: IETF draft-shabazz-http-x402-tswp-00, Solana SIMD #671, XRPL XLS #646, Zenodo DOI 10.5281/zenodo.22979715
---
# The X402 Typed Settlement Wire Protocol over Interledger
## Abstract
This specification defines the integration of the **X402 Typed Settlement Wire Protocol (X402-TSWP)** within the **Interledger Protocol (ILPv4)** architecture. It establishes a standardized mechanism for machine-to-machine (M2M) challenge-response paywalls (HTTP status code `402 Payment Required`), payment pointer resolution, and cryptographic condition-fulfillment validation across ILP-connected ledger networks (including Solana Token-2022 and the XRP Ledger).
---
## 1. Motivation
The Interledger Protocol (ILP) defines a multi-hop, packetized value transfer network across heterogeneous ledgers. The Simple Payment Setup Protocol (SPSP) and Open Payments standard provide higher-level interfaces for querying payment setup information over HTTP.
However, existing ILP application-layer protocols face several operational gaps when interfacing with autonomous software agents and high-throughput financial execution engines:
1. **Lack of Structured In-Band Challenge Negotiation:** While HTTP 402 is referenced conceptually, there is no standardized, byte-exact schema for servers to issue single-use challenge tokens, pricing matrices, and multi-rail fulfillment criteria within standard HTTP/JSON-RPC error exchanges.
2. **Missing SWIFT / ISO 20022 Linkage:** Cross-border institutional settlements transiting through ILP connectors lack a deterministic, byte-exact grammar to bind ILP packets to SWIFT Unique End-to-End Transaction References (UETRs).
3. **Regex Fragility on Execution Engines:** High-performance L1 blockchains connected to ILP (such as Solana) cannot afford off-chain regex string parsing for packet memo introspection.
X402-TSWP resolves these challenges by introducing a formal, byte-exact ABNF operational grammar and ILP fulfillment binding.
---
## 2. Protocol Integration with ILPv4
### 2.1. The X402 Challenge-Response Flow
Client (AI Agent / Payer) Server (Merchant / Tool Provider) | | |---- 1. HTTP GET / Resource (Unauthenticated) ------->| | | |<--- 2. HTTP 402 Payment Required --------------------| | (Headers: X-402-Challenge, X-402-Pricing; | | Body: SPSP / Open Payments metadata) | | | |---- 3. Resolve SPSP / Payment Pointer -------------->| |<--- 4. Return ILP Shared Secret & Condition ---------| | | |==== 5. Execute ILP Packet / Blockchain Settlement ==>| | (Carrying byte-exact memo: X402G:) | | | |---- 6. HTTP GET / Resource (With X-402-Payment) ---->| |<--- 7. HTTP 200 OK (With X-402-Receipt) -------------|



### 2.2. Header Specification
#### Request Headers:
- `X-402-Payment`: Contains the proof-of-settlement descriptor.
  - Format: `<scheme>:<rail>:<tx-hash-or-fulfillment>:<challenge-uuid>`
  - Example: `x402:ilp-stream:f47ac10b...827da995-adda-4dd7-9fb5-d05338526873`
#### Response Headers (HTTP 402):
- `X-402-Challenge`: The cryptographically random RFC 4122 UUIDv4 challenge token.
- `X-402-Pricing`: Price per invocation expressed in standardized units (e.g., `160:drops` or `1000:lamports`).
- `X-402-PayTo`: The recipient ILP payment pointer (e.g., `$wallet.synapticchain.xyz/settle`) or destination ledger address.
- `X-402-Memo`: The exact byte-exact preimage required in the carrier packet:
X402G:



---
## 3. Wire Grammar & ILP Data Payload
When settling over an ILP STREAM packet, the `X402` discriminator is injected into the packet data frame:
```abnf
x402-ilp-data   = "X402" discriminator ":" payload
discriminator   = "G" / "W" / "L" / "M"
payload         = 1*128(ALPHA / DIGIT / "-" / ":")
Supported Codecs:
X402G:<challenge>: Gateway challenge micropayment. Binds an ILP transfer to an ephemeral HTTP 402 challenge.
X402W:<window>:<uetr>: Multilateral netting settlement. Cryptographically links an ILP clearing batch to an ISO 20022 SWIFT gpi UETR.
X402L:<lane>:<window>:<nonce>: Parallel lane execution. Directs funds across 256 concurrent execution lanes under the ADR-062 sliding window without account lock contention.
4. Multi-Rail Settlement Mapping
X402-TSWP over Interledger operates symmetrically across the following underlying settlement rails:

Ledger / Rail	Interledger Prefix	Carrier Field	Operational Check
Solana Token-2022	g.crypto.solana	SPL Memo v2	sysvar::instructions index 0 byte-exact match + RequiredMemoTransfers
XRP Ledger	g.crypto.ripple	Transaction Memos array	MemoType == hex("X402"), MemoData == hex(X402G:<challenge>)
ILP STREAM	g.	STREAM Data Frame	Byte-exact match on data payload preceding frame fulfillment
5. Security & Invariants
Non-Replayability: Every X-402-Challenge is single-use and transitions to Settled or Expired upon the first ledger confirmation.
Byte-Exact Equality: Connectors and gateways MUST NOT perform fuzzy or substring matching. Equality evaluation MUST be byte-exact.
Solvency Invariant: All netting windows MUST adhere to zero-leakage solvency (
∑
Debits
=
=
∑
Credits
∑Debits==∑Credits, 
Δ
=
0
Δ=0).
6. Prior Art & Reference Implementations
IETF Standards Track: draft-shabazz-http-x402-tswp-00
Solana Foundation SIMD: Solana SIMD PR #671
XRPL Standards: XLS Discussion #646
Permanent Defensive Prior Art: Zenodo DOI 10.5281/zenodo.22979715
Reference Gateway: mcp-402-gateway (:8405) / syn-m2m-server
