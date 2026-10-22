# Papers kept in this repository

Unmodified copies of papers the design documents rely on, kept so that agents can read them without
network access. Each is redistributed under its own licence, named below; cite the original.

| File | Paper | Source and licence | Why it is here |
|---|---|---|---|
| [`CGSY24-security-bounds-for-proof-carrying-data-from-straightline-extractors-ePrint-2023-1646.pdf`](CGSY24-security-bounds-for-proof-carrying-data-from-straightline-extractors-ePrint-2023-1646.pdf) | Alessandro Chiesa, Ziyi Guan, Shahar Samocha, Eylon Yogev, *Security Bounds for Proof-Carrying Data from Straightline Extractors*, a major revision of the TCC 2024 paper | IACR ePrint [2023/1646](https://eprint.iacr.org/2023/1646), the revision of 2024-09-11 (the date on its title page); licence [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), as stated on the ePrint page (checked 2026-10-22). SHA-256 `78faaa96fcb06858ac10dd213e47ccbaa4b90959f596af03560f02451ab47f0d`. Supplied by the user; not byte-compared with ePrint's copy, which served a bot challenge | the tree theorem (Thm 1, formally Thm 5.1) behind the attested and signed oracle designs; the signed random oracle model (§2.2, §6.2); the non-succinct "trace in the proof" construction (§2.3, Construction 6.8). Read with [the CGH circumvention guide](../../CGH-circumvention-guide-secret-keyed-signed-and-attested-random-oracles-with-reading-list.md) and [`DESIGN-relativized-recursion.md`](../../DESIGN-relativized-recursion.md) §4.6 |

Before adding a paper, check that its licence allows redistribution (many ePrint papers are CC BY;
some are not), record the licence and the version, and prefer a link when the licence is unclear.
