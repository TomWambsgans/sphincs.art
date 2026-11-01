# leanSPHINCS proofs in Lean 4

**Status: the leanSphincs signer has 127 bits of classical SUF-CMA security in the random-oracle
model in each of its configurations, at the signature limits below: one theorem per height, shape and kept
subtree height (and forest size for the layered keys of 2^24 and 2^26), 39 in all, stated together in [Main.lean](LeanForest/Main.lean); the FORS variant has its own 39 in
[FORS/Main.lean](FORS/Main.lean). Both also have 100 bits at larger limits, within 0.1% of the cover attack at
100 bits (39 more theorems each, below).** The
proof uses only `propext`, `Classical.choice` and `Quot.sound`: [Axioms.lean](LeanForest/Axioms.lean)
pins the main theorems to their axioms and checks that no declaration of the library uses another.

**To audit the statement**, read three files: [Main.lean](LeanForest/Main.lean) (what is proved,
`Secure127`, and the 39 theorems, e.g. `h24_pruned12`, then `requestedSecurity`, which collects
them), [Scheme.lean](LeanForest/Scheme.lean) (the scheme and its parameters, `Params.pruned` and
`Params.layered`) and [Statement.lean](LeanForest/Statement.lean) (the SUF-CMA game). Every
other file is proof: [PROOF.md](PROOF.md) maps it.

`LeanForest/` models the candidate for every height `h ≤ 28`, number of layers `d` and kept subtree
height `b` (`Params`, [Scheme.lean](LeanForest/Scheme.lean)): an index of `h` bits; a hypertree of
`d` layers of WOTS+C keys (64 chains of four positions, target sum 128), whose layers below the top
share one height `ℓ ≥ 6` (`lowerHeight`) and whose top layer has the rest; a two-level WOTS forest of `T ≤ 8` trees (its coordinates, `forestCoords`) as the few-time signature; one
message-digest call; and pruning of the top layer with surrogate siblings. A pruned key is `d = 1`,
`b ≤ h` (`b = h` is the full key); a layered key keeps everything, `b = h`, `d ≥ 2`. No tree of the
forest has a root hash and the forest key is not hashed: the WOTS+C encoding of the bottom layer
absorbs its 2T nodes with the counter last, and the encoding of a higher layer the root of the
tree below. Every hash input is the 16-byte public parameter P, a 16-byte address (4 bytes `lo`,
3 bytes `hi`, one byte type + 32·step, one byte for the layer counted from the bottom, 4 bytes for
the tree, then 3 zero bytes) and the payload. One hash of the seed gives two secrets, the two
16-byte halves of its output. The signer derives R0 and the step δ from one hash
H(P ‖ A(7, 0, 0) ‖ seed ‖ m) per message and tries R0, R0 + δ, R0 + 2δ, … until the digest index
lands in the kept subtree, as the Rust signer does, so a repeated request returns the same
signature. δ is odd, so the walk does not come back within 2^128 attempts (`walk_iterate_ne`), and
secret, so a signature does not tell which randomizers were rejected before it. The SUF-CMA game is
[Statement.lean](LeanForest/Statement.lean): for every adversary, if the whole game makes q ≥ 1 hash
queries in total (the adversary's, and those of keygen, signing and verification), a forgery has
probability at most q / 2^127.

The proof is the same for every hash: the random oracle stands for Keccak-256, BLAKE2s or SHA-256,
and only the costs depend on the hash ([Scheme/VerificationCost.lean](LeanForest/Scheme/VerificationCost.lean),
[Configurations.lean](LeanForest/Configurations.lean)). So the 30 configurations of the candidate
(5 lifetimes, 2 shapes, 3 hashes) take 39 lifetime theorems (per lifetime: the full key, six kept subtree
heights, five at 2^24, and the layered key, below), 10 size theorems and 30 cost theorems.

The scheme, the digest layout, the codeword table, the costs and the forest are documented in
[FOREST.md](FOREST.md); the proof route and the modeling differences with the Rust code are in
[PROOF.md](PROOF.md). `FORS/` is the same proof with FORS (24 trees of height 10; 19 and 23 trees of
height 9 for the layered keys of 2^24 and 2^26) as the
few-time signature: what FORS changes, and what that changes in the proof, is
in [FORS.md](FORS.md).

## Proved lifetimes

Signature limits N with 127 bits (one theorem each in [Main.lean](LeanForest/Main.lean), e.g.
`h24_pruned12`). A pruned key has height h = log2(lifetime) − 4; the layered key of each lifetime is 10 + 7 + 7
(h = 24) up to 2^28, then 10 + 8 + 8 and 10 + 9 + 9, with a forest of 6 and 7 trees at 2^24 and 2^26 (8
otherwise).

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 19,830,000 | — | 371,400 | 191,200 | 98,480 | 26,080 | 6,926 | 26,670,000 |
| 2^26 | 22 | 81,860,000 | 21,760,000 | 405,300 | 208,500 | 107,200 | 28,410 | 7,514 | 144,300,000 |
| 2^28 | 24 | 336,700,000 | 23,830,000 | 441,500 | 226,800 | 116,600 | 30,810 | 8,154 | 336,700,000 |
| 2^30 | 26 | 1,381,000,000 | 26,030,000 | 480,100 | 246,900 | 126,900 | 33,480 | 8,830 | 1,381,000,000 |
| 2^32 | 28 | 5,634,000,000 | 28,350,000 | 522,000 | 267,900 | 137,400 | 36,190 | 9,541 | 5,634,000,000 |

As a share of the lifetime in the cover model (the attack that covers a forest instance; at h = 24
the best known attack, with the WOTS+C unit-neighbour route, is 91–100% of it; FOREST.md):

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 88.2% | — | 83.4% | 82.6% | 81.9% | 80.6% | 79.5% | 60.0% |
| 2^26 | 22 | 91.0% | 89.2% | 84.3% | 83.6% | 82.8% | 81.5% | 80.2% | 85.6% |
| 2^28 | 24 | 93.5% | 90.3% | 85.2% | 84.4% | 83.7% | 82.3% | 81.1% | 93.5% |
| 2^30 | 26 | 95.9% | 91.3% | 86.1% | 85.4% | 84.7% | 83.2% | 81.9% | 95.9% |
| 2^32 | 28 | 97.8% | 92.1% | 87.1% | 86.3% | 85.4% | 83.9% | 82.6% | 97.8% |

The full key lasts about 21.45 · 2^h signatures in the cover model; a layered key of 8 trees has the
same limit, since the proof only charges its smaller key generation. The lighter layered keys of 2^24 and 2^26
are proved further from their cover attack than the 8-tree layered keys (60.0% and 85.6%, against 93.5–97.8%), still well above 2^24 and 2^26. A pruned key loses less than its
pruning factor 2^(h−b): the forger must land in the kept subtree as well.

These figures do not depend on how the signer picks its randomizer. The proof fixes the steps δ of
all messages and averages only the starts R0 (`Det.forgeAdvantage_le_seedFree`): the bound holds
for every table of steps, as if the forger knew them.

## Proved lifetimes, FORS variant

The same statement for the `FORS` library ([FORS.md](FORS.md)): one
theorem per height, shape, kept subtree height and FORS shape in [Main.lean](FORS/Main.lean), 39 in all, collected by
`requestedSecurity`, with [Axioms.lean](FORS/Axioms.lean) pinning them to the same three axioms.

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 17,650,000 | — | 327,400 | 168,300 | 86,430 | 22,850 | 6,036 | 16,777,216 |
| 2^26 | 22 | 72,220,000 | 19,240,000 | 356,000 | 182,800 | 93,890 | 24,790 | 6,547 | 73,380,000 |
| 2^28 | 24 | 293,000,000 | 20,920,000 | 387,200 | 198,700 | 101,900 | 26,860 | 7,099 | 293,000,000 |
| 2^30 | 26 | 1,182,000,000 | 22,750,000 | 419,700 | 215,400 | 110,500 | 29,130 | 7,677 | 1,182,000,000 |
| 2^32 | 28 | 4,731,000,000 | 24,710,000 | 455,600 | 233,500 | 119,800 | 31,600 | 8,313 | 4,731,000,000 |

These are 82.7–98.3% of the FORS cover attack, in every configuration a larger share than the forest's limit is
of the forest's attack. They are 11–16% below the forest's limits, except for the layered keys of 2^24 and 2^26
(19×9 and 23×9 against forests of 6 and 7 trees): 37% and 49% below. The layered key of 2^24 is proved
through a third route between the small and the large one, the survival-weighted route
(`ForsPotential.det_bitsF3`, [FORS.md](FORS.md)).

## Proved lifetimes at 100 bits

The same claim at a lower target, `Secure100` (forgery probability at most `q / 2^100`), for the same 39
configurations of each variant: `requestedSecurity100` in [Main.lean](LeanForest/Main.lean) and in
[FORS/Main.lean](FORS/Main.lean), one theorem each (e.g. `h24_pruned12_100`). A target of 100 bits
constrains only the budgets `q < 2^100`, which the small route alone covers: `ForestPotential.det_bitsS`
([Certificates/ClosingBits](LeanForest/Certificates/ClosingBits.lean), and `ForsPotential.det_bitsS` for
FORS) is the small-route bound `det_smallF` compared with `q / 2^bits` instead of `q / 2^127`, with one
rational check per configuration (`checkSmallS`, [Certificates/Bits100](LeanForest/Certificates/Bits100)).
The generic searches that cost the 127-bit proofs up to 20% (about `2^-127` per query) are `2^-27` of
this budget, so the limits are the cover attack at 100 bits to within 0.1%: the signature count at
which one digest query covers an instance with probability `2^-100` (Poisson loads for the forest,
exact binomial loads for FORS). The moment tables reach `n ≤ 255` signatures per instance for these
loads.

Forest:

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 59,850,000 | — | 1,135,000 | 585,900 | 302,300 | 80,480 | 21,410 | 303,300,000 |
| 2^26 | 22 | 239,400,000 | 63,890,000 | 1,209,000 | 624,000 | 321,900 | 85,650 | 22,770 | 603,400,000 |
| 2^28 | 24 | 957,700,000 | 68,150,000 | 1,287,000 | 664,200 | 342,600 | 91,100 | 24,210 | 957,700,000 |
| 2^30 | 26 | 3,830,000,000 | 72,650,000 | 1,370,000 | 706,700 | 364,400 | 96,860 | 25,730 | 3,830,000,000 |
| 2^32 | 28 | 15,320,000,000 | 77,400,000 | 1,457,000 | 751,500 | 387,400 | 102,900 | 27,340 | 15,320,000,000 |

As a share of the cover attack at 100 bits:

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 99.99% | — | 99.97% | 99.99% | 99.98% | 99.99% | 99.99% | 100.00% |
| 2^26 | 22 | 99.99% | 99.99% | 99.96% | 99.99% | 99.99% | 100.00% | 99.97% | 99.99% |
| 2^28 | 24 | 100.00% | 99.99% | 99.94% | 99.99% | 100.00% | 100.00% | 99.98% | 100.00% |
| 2^30 | 26 | 99.97% | 99.99% | 99.97% | 100.00% | 100.00% | 100.00% | 99.98% | 99.97% |
| 2^32 | 28 | 99.97% | 99.99% | 99.95% | 99.99% | 99.99% | 99.96% | 100.00% | 99.97% |

FORS variant:

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 51,330,000 | — | 987,800 | 511,100 | 264,400 | 70,800 | 18,940 | 126,800,000 |
| 2^26 | 22 | 205,300,000 | 55,040,000 | 1,057,000 | 547,400 | 283,200 | 75,780 | 20,270 | 296,100,000 |
| 2^28 | 24 | 821,300,000 | 59,000,000 | 1,132,000 | 586,000 | 303,100 | 81,090 | 21,690 | 821,300,000 |
| 2^30 | 26 | 3,285,000,000 | 63,210,000 | 1,212,000 | 627,100 | 324,300 | 86,760 | 23,200 | 3,285,000,000 |
| 2^32 | 28 | 13,140,000,000 | 67,710,000 | 1,297,000 | 671,000 | 347,000 | 92,800 | 24,810 | 13,140,000,000 |

As a share of the FORS cover attack at 100 bits:

| lifetime | h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered (h ≥ 24) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^24 | 20 | 99.99% | — | 100.00% | 99.98% | 99.96% | 99.99% | 99.92% | 99.98% |
| 2^26 | 22 | 99.98% | 99.99% | 99.90% | 100.00% | 100.00% | 99.98% | 99.94% | 99.99% |
| 2^28 | 24 | 99.99% | 99.99% | 99.93% | 100.00% | 99.99% | 99.98% | 99.96% | 99.99% |
| 2^30 | 26 | 99.99% | 99.98% | 99.96% | 99.99% | 99.97% | 99.99% | 99.96% | 99.99% |
| 2^32 | 28 | 99.99% | 100.00% | 99.96% | 99.99% | 99.99% | 99.99% | 99.96% | 99.99% |

## Checked claims

| Claim | Theorem / file |
| --- | --- |
| **127-bit SUF-CMA security at the limits above** | `requestedSecurity`, [Main](LeanForest/Main.lean) |
| **100-bit SUF-CMA security at the limits at 100 bits** | `requestedSecurity100`, [Main](LeanForest/Main.lean) |
| At `bits ≤ 127` bits, one small-route check at `qh ≥ 2^bits − 1` suffices | `ForestPotential.det_bitsS`, [Certificates/ClosingBits](LeanForest/Certificates/ClosingBits.lean); certificates in [Certificates/Bits100](LeanForest/Certificates/Bits100) |
| The bound follows from rational checks on two budget routes, for any height, shape and hash | `ForestPotential.det_bitsFH`, [Certificates/Closing](LeanForest/Certificates/Closing.lean); certificates in [Certificates](LeanForest/Certificates) |
| The deterministic signer reduces to a seed-free game of an adversary that never repeats a message | `Det.forgeAdvantage_le_seedFree`, [Reduction/SeedElimination](LeanForest/Reduction/SeedElimination.lean) |
| An accepted forgery is classified layer by layer, from the top | `SignatureWitness.accepted_full_classification`, [Classification/Accepted](LeanForest/Classification/Accepted.lean) |
| Key generation makes exactly 226·2^k + 2(t − k) hash calls (top layer of height t, kept height k) | `Prefix.hashCalls_keygenFromSeed`, [GraphView/HashCalls](LeanForest/GraphView/HashCalls.lean) |
| The digest's index and the 26-bit field of each of the T trees are a bijection of its h + 26T bits | `fullDigestView_bijective`, [Scheme/DigestView](LeanForest/Scheme/DigestView.lean) |
| A successful seeded signature verifies | `Completeness.correct`, [Scheme/Correctness](LeanForest/Scheme/Correctness.lean) |
| Computed subtree and surrogate path recover the root, at every layer | `Completeness.eval_treeFold_pruned_path`, [Scheme/Pruning](LeanForest/Scheme/Pruning.lean) |
| Serialized signature length = 16 + 352·T + 1028·d + 16·h bytes | `signature_size`, [Scheme/Layout](LeanForest/Scheme/Layout.lean) |
| An accepted verification costs exactly `verifyCost` compressions of each hash (at most that for any signature) | `Cost.verification_compressions`, [Scheme/VerificationCost](LeanForest/Scheme/VerificationCost.lean) |
| The size and the three verification costs of each of the 10 shapes | [Configurations](LeanForest/Configurations.lean) |

## Build

```sh
cd formal/sphincs
env LEAN_NUM_THREADS=1 nice -n 19 lake exe cache get
env LEAN_NUM_THREADS=1 nice -n 19 lake build LeanForest FORS
```

No `sorry`, `native_decide`, or new axioms are used. The certificates of one height take about
30–50 s and 1 GB of memory (forest), or 2.5–4 min and 7 GB (FORS); those at 100 bits, 30–55 s.

The numeric certificates are generated by `python3 scripts/forest_certificates.py emit` (pure
Python, exact rationals), which rewrites `LeanForest/Certificates/H*.lean` and
`LeanForest/Lifetimes.lean` (one proof per configuration; [Main.lean](LeanForest/Main.lean), written
by hand, states them); the kernel re-checks them with `decide +kernel` during the build.
`python3 scripts/fors_certificates.py emit-lifetimes` does the same for `FORS`, with the three-route
certificate `Certificates/H24SW.lean` (plain emit writes only the certificates), from the closed-form moments of a FORS tree instead of a codeword table. `scripts/forest_table.py` writes the codeword table.
`emit-bits 100` (both scripts) writes the certificates at 100 bits, `Certificates/Bits100/H*.lean` and
`Lifetimes100.lean`, from the limits `PARAMS_BITS` that `maxn-bits` found.
`lake env lean scripts/Reach.lean` writes `reach.txt`, which declarations the pinned theorems and
the cited names reach; `python3 scripts/doc_check.py` then checks that these docs cite only existing
files and Lean names.

## Credit

`LeanForest` and `FORS` adapt the security proof of leanVM's three-layer scheme
([leanVM](https://github.com/leanEthereum/leanVM) at commit `b7a107256`, MIT OR Apache-2.0, see
[licenses](../../licenses)); that proof, the `SphincsSecurity` library, is in this repository's
history at commit `7269bd3`.
