# CONTRIBUTING

Contributions to the Interledger RFC repo are subject to the following copyright and licensing terms and follow the following document publishing process.

## Summary

Copyright on all content is subject to the terms of the [CC-BY-SA 4.0 license](LICENSE).
IP is subject to the terms of the [W3C Contributor License Agreement](https://www.w3.org/community/about/agreements/cla/).

All contributors grant everyone:

Copyright – a royalty-free license to use the copyrights for their contributions.
Patent – a commitment to license on a royalty-free basis their essential patent claims reading on their contributions.

## Background

The work of the Interledger community is being done under the framework of a W3C Community Group and is therefore guided by the [processes](https://www.w3.org/community/about/agreements/) laid out by the W3C for these groups.

Also influencing this process is the well-established and popular IETF RFC process.

## Process

The ILP RFC process attempts to be easy to use but also rigorous enough that there are permalinks to revisions of documents for reference purposes.

The process differentiates between specifications that are incubating (similar to IETF Internet Drafts) and those that are mature (similar to IETF RFCs).

Theare are three document types: *Proposals*, *Working Drafts*, and *Candidate Specifications*.

### Proposals
A _Proposal_ is an RFC document that proposes some new feature, protocol or idea related to Interledger. The criteria for getting a proposal document merged is minimal: project maintainers will review the document to ensure style conformance and applicability to Interledger standards, but will otherwise require not require editorial fixes before allowing a proposal to be published.

#### Publish a Proposal
To publish a new Proposal, submit a Pull Request to the [RFC Proposals repo](https://github.com/interledger/rfcs/proposals) with a new Markdown file. The file MUST follow the naming convention `0000-title`, where title is a lower case title with spaces replaced by hyphens (`-`), and have front-matter (similar to GitHub pages rendered from MarkDown) specifying at least a `title` and `draft` (an integer, starting at 1 and incrementing with each revision of the RFC).

Example:
```markdown
\---
title: The Interledger Architecture
type: proposal
draft: 1
\---
# Interledger Architecture

Lorum Ipsum etc
```

### Working Drafts 
A _Working Draft_ is an RFC that has gained significant consensus support from the Interledger community. Working Drafts differ from Proposals in that edits to the document undergo significant community review and are not merged until there is broad consenus among the editors of the RFC, and the broader Interledger community.

#### Publishing a Working Draft
Assuming there is consensus to publish, one of the project maintainers will review the submission and assign an RFC number to the document, making a follow up commit to the PR which renames the file as appropriate. 

The maintainer will move the document into the [RFC Working Drafts repo](https://github.com/interledger/rfcs/working-drafts). Subsequent updates to the document will trigger a publishing workflow that creates an HTML rendered version of the document that contains a permalink to the draft. Each revision must increment the `draft` number in the front-matter or the publishing will fail.

Example:
```markdown
\---
title: The Interledger Architecture
type: working-draft
draft: 2
\---
# Interledger Architecture

Lorum Ipsum etc
```

### Candidate Specifications
A _Candidate Specification_ is a document that was previously a Working Draft RFC that was considered stable enough by the community such that no further changes are required. Once an RFC becomes a Candidate Specification, no further substantive changes are allowed under the same RFC number, and the draft number changes to FINAL.

#### Publishing a Candidate Specification
When a Working Draft is considered stable there is a call for review from the community to publish the document as a Candidate Specification.

Assuming there is consensus to publish, a maintainer will move the document into the [RFCs repo](https://github.com/interledger/rfcs). Once published as a Candidate Specifiation, no further substantive changes are allowed under the same RFC number (the draft number changes to FINAL).

Candidate Specifications may also be published in a W3C Community Group report and may be published as an IETF Internet Draft, if appropriate.

Note that a different template is used for Working Drafts and Candidate Specifications to help readers differentiate between them.

Example:
```markdown
\---
title: The Interledger Architecture
type: candidate-specification
draft: FINAL
\---
# Interledger Architecture

Lorum Ipsum etc
```

### Rejected RFCs
An RFC document may be rejected phase after public discussion has settled and comments have been made summarizing the rationale for rejection. A member of the core team will move rejected proposals to the [/rejected](https://github.com/interledger/rfcs/rejected) folder in this repo.
