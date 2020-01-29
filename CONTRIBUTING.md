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

There are three document types: *Proposals*, *Working Drafts*, and *Candidate Specifications*. The status of any particular RFC has no bearing on the priority of that RFC, although typically the further along in the RFC process, the more likely it is that any particular RFC will be implemented.

### Proposals
A _Proposal_ is an RFC document that proposes some new feature, protocol or idea related to Interledger. The criteria for getting a proposal document merged is minimal: project maintainers will review the document to ensure style conformance and applicability to Interledger standards, but will otherwise not require editorial fixes before allowing a proposal to be published.

#### Publishing a Proposal
To publish a new Proposal, submit a Pull Request to the [/proposals](https://github.com/interledger/rfcs/proposals) folder with a new Markdown file. The file MUST follow the naming convention `0000-{title}`, where `title` is a lower case title with spaces replaced by hyphens (`-`). The submission must have front-matter (similar to GitHub pages rendered from MarkDown) specifying at least a `title`, `type`, and `draft` (an integer, starting at 1 and incrementing with each revision of the RFC). The `type` MUST have the value `proposal`.

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
A _Working Draft_ is an RFC that has become stable enough for people to experiment with, but has not necessarily been endorsed by the entire community. Working Drafts differ from Proposals in that edits to the document undergo significant community review and are not merged until there is at least broad consensus among the editors of the RFC. In this way, it should be possible to have two competing Working Drafts that address the same problem in different ways, either or both of which may graduate into a Candidate Specification.

Because Working Drafts change much less frequently than a Proposal, implementors can begin creating software to implement 
this type of RFC into their codebase to explore how it works in a real world setting.

Note that a Working Draft RFC is not a [rubber-stamp](https://idioms.thefreedictionary.com/rubber-stamp) of the content
 in any particular RFC. Documents can still undergo significant changes and potentially be discarded all together.

#### Publishing a Working Draft
Assuming there is consensus to publish, one of the project maintainers will review the submission and assign an RFC number to the document, making a follow up commit to the PR which renames the file as appropriate. 

The maintainer will move the document into the [RFC Working Drafts repo](https://github.com/interledger/rfcs/working-drafts) and update the `type` to be `working-draft`. 

Subsequent updates to the document will trigger a publishing workflow that creates an HTML rendered version of the document that contains a permalink to the draft. Each revision must increment the `draft` number in the front-matter or the publishing will fail.

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
A _Candidate Specification_ is a document that was previously a Working Draft RFC that is considered stable enough by the community such that no further changes are required. Once an RFC becomes a Candidate Specification, no further substantive changes are allowed under the same RFC number, and the draft number changes to FINAL.

#### Publishing a Candidate Specification
When a Working Draft is considered stable there is a call for review from the community to publish the document as a Candidate Specification.

Assuming there is consensus to publish, a maintainer will move the document into the [RFCs repo](https://github.com/interledger/rfcs) and update the `type` to `candidate-specification`. 

Once published as a Candidate Specification, no further substantive changes are allowed under the same RFC number (the draft number changes to FINAL).

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

#### Errata
Sometime the community will discover errors in an RFC that has been designated as a Candidate Specification and marked final. In these circumstances, it is possible to udpate an RFC to fix typos or enhance the original meaning of an RFC. In these circumstances, an errata indicator MUST be added to the RFC's front-matter to indicate an errata version, like this:

Example:
```markdown
\---
title: The Interledger Architecture
type: candidate-specification
draft: FINAL
errata: 1
\---
# Interledger Architecture

Lorum Ipsum etc
```


### Rejected RFCs
An RFC document may be rejected after public discussion has settled and comments have been made summarizing the rationale for rejection. A member of the core team will move rejected proposals to the [/rejected](https://github.com/interledger/rfcs/rejected) folder in this repo.

## Gathering Feedback Before Submitting
It is often helpful to get feedback on your concept before submitting an actual PR. You may open an issue on this repo 
to start a high-level discussion, or start a conversation with other community members in the [Interledger Slack](https://communityinviter.com/apps/interledger/interledger-working-groups-slack) if you 
want to get community input before submitting a proposal.
