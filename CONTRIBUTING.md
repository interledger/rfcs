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

The two document types are *Working Drafts* and *Candidate Specifications*.

1. When a community member wishes to submit a new document for comment they will submit a Pull Request to the [RFCs repo](https://github.com/interledger/rfcs/) which adds a new Markdown file. The file MUST follow the naming convention `0000-title`, where title is a lower case title with spaces replaced by hyphens (`-`), and have front-matter (similar to GitHub pages rendered from MarkDown) specifying at least a `title` and `draft` (an integer, starting at 1 and incrmenting with each revision of the RFC).

Example:
```
---
title: The Interledger Architecture
draft: 1
---
# Interledger Architecture

Lorum Ipsum etc
```

2. One of the project maintainers will review the submission and assign an RFC number to the document, making a follow up commit to the PR which renames the file and folder as appropriate.

3. Subsequent updates to the document will trigger a publishing workflow that creates an HTML rendered version of the document that contains a permalink to the draft. Each revision must increment the `draft` number in the front-matter or the publishing will fail.

4. These Interledger RFCs are living documents that start as Working Drafts and are iterated on until they are considered stable.

5. *Working Drafts* have an RFC number AND a draft number starting at 1 and increasing by 1 each time the content is changed.

6. When a Working Draft is considered stable there is a call for review from the community to publish the document as a *Candidate Specification*.

7. Assuming there is consensus to publish, the document becomes a *Candidate Specification* and no further substantive changes are allowed under the same RFC number. (The draft number changes to `FINAL`).

8. *Candidate Specifications* will also be published as W3C Community Group reports and may be published as IETF Internet Drafts if appropriate.

9. A different template is used for *Working Drafts* and *Candidate Specifications* to help readers differentiate between them.
