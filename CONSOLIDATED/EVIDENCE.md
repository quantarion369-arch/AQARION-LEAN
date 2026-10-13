# AQARION Lean — Evidence Ledger

## AQFPR006

### Source repair

- Replaced unsafe List.get! usage with bounded indexing.
- Corrected the restricted-growth-string empty-prefix case.
- Verified partitions 3 produces exactly five set partitions.

### Finite anchors

The following weighted-Bell anchors passed:

- weightedBell [1,1,2] = 7
- weightedBell [2,2] = 7
- weightedBell [2,2,2] = 31
- weightedBell [2,4] = 9
- weightedBell [3,3] = 8

These are labeled native_decide computational checks, not a completed general proof.

### Gate 2

- Baseline build exit: 0
- Mutation build exit: 1
- Restored build exit: 0
- Mutation: listGcd block replaced by block.foldl Nat.lcm 1
- Witness: listGcd [2,4] = 2, while lcm [2,4] = 4

The mutation was detected because it changed the weighted-Bell result and caused an anchor to fail.

## PB006Audit

PB006Audit transferred successfully and rebuilt successfully in the current environment.

Prior artifacts include pb006bench and hash files. The fresh rebuild is recorded separately from those prior artifacts.

## PBCore006

PBCore006 transferred successfully and rebuilt successfully in the current environment.

Its mathematical interpretation remains open. A successful build does not establish the intended coefficient theorem.

## Evidence capsules

- EVIDENCE_BURNSIDE_MOMENTS.json: finite Burnside-moment calculations.
- BURNSIDE_MOMENTS_k1_10.json: cycle-type and partition-sum checks through k = 10.
- MODULAR_ATLAS_LINEAR_605.json: 605 modular cases with zero disagreements.
- QUADRATIC_CRITERION.json: recorded modular quadratic criterion and distinguishing example.
- aqarion_receipt.json: broader AQARION receipt with finite checks and mutation results.

These are finite computational evidence records, not Lean proofs or promotion certificates.
