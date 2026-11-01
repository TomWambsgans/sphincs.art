import LeanForest.Lifetimes
import LeanForest.Lifetimes100

/-!
# leanSPHINCS: every security theorem

This file states every security theorem of the library: one theorem per height, shape and kept
subtree, 39 in all, then `requestedSecurity`, which collects them. The proofs live elsewhere
(`Lifetimes.lean`, from the certificates of `Certificates/`); here each one is a single reference,
so a statement below that is not exactly the one proved does not typecheck.

**What is proved.** `Secure127 P` (below) for the scheme with parameters `P`: in the SUF-CMA game
(`Statement.lean`), the adversary gets the public key, the hash (a random oracle) and a signing
oracle that it may ask for at most `N` signatures (the signature limit of `P`); it wins if it
outputs a message and a signature that verify, other than a pair the signing oracle answered. If
every run of the game makes at most `q ≥ 1` hash queries in total (the adversary's, and those of key
generation, signing and verification), it wins with probability at most `q / 2^127`.

**The parameters** (`Scheme.lean`). Every key has an index of `h` bits, `h ∈ {20, 22, 24, 26, 28}`:
* `.pruned (h := h) (b := h) (N := N)`: the **full key**, one tree of height `h`, all built;
* `.pruned (h := h) (b := b) (N := N)`: a **pruned key**, the same tree, of which key generation
  builds only a subtree of height `b`; the signer grinds its randomizer until the index lands in it;
* `.layered (h := h) (d := 3) (ℓ := ℓ) (N := N)`: a **layered key**, three layers, the two lower
  ones of height `ℓ` and the top one of height `h - 2ℓ`; at `h = 24` also with a forest of `T = 6` or
  `T = 7` coordinates (`(T := T)`, the uniform keys of the `2^24` and `2^26` lifetimes), 8 otherwise.

**The hash** is not a parameter: the random oracle stands for Keccak-256, BLAKE2s and SHA-256
alike, so each theorem covers the three hashes. Sizes and verification costs, which depend on the
hash, are in `Configurations.lean`.
-/

namespace LeanForest

open Security ENNReal

/-- **The claim**, for the scheme with parameters `P`: every adversary whose runs of the SUF-CMA game
make at most `q ≥ 1` hash queries in total forges with probability at most `q / 2^127`. -/
def Secure127 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-! ## h = 20 -/

/-- Full key: 19,830,000 signatures. -/
theorem h20_full : Secure127 (.pruned (h := 20) (b := 20) (N := 19_830_000)) := Lifetimes.h20_full_bits
/-- Pruned key, kept subtree of height 14: 371,400 signatures. -/
theorem h20_pruned14 : Secure127 (.pruned (h := 20) (b := 14) (N := 371_400)) := Lifetimes.h20_pruned14_bits
/-- Pruned key, kept subtree of height 13: 191,200 signatures. -/
theorem h20_pruned13 : Secure127 (.pruned (h := 20) (b := 13) (N := 191_200)) := Lifetimes.h20_pruned13_bits
/-- Pruned key, kept subtree of height 12: 98,480 signatures. -/
theorem h20_pruned12 : Secure127 (.pruned (h := 20) (b := 12) (N := 98_480)) := Lifetimes.h20_pruned12_bits
/-- Pruned key, kept subtree of height 10: 26,080 signatures. -/
theorem h20_pruned10 : Secure127 (.pruned (h := 20) (b := 10) (N := 26_080)) := Lifetimes.h20_pruned10_bits
/-- Pruned key, kept subtree of height 8: 6,926 signatures. -/
theorem h20_pruned8 : Secure127 (.pruned (h := 20) (b := 8) (N := 6_926)) := Lifetimes.h20_pruned8_bits

/-! ## h = 22 -/

/-- Full key: 81,860,000 signatures. -/
theorem h22_full : Secure127 (.pruned (h := 22) (b := 22) (N := 81_860_000)) := Lifetimes.h22_full_bits
/-- Pruned key, kept subtree of height 20: 21,760,000 signatures. -/
theorem h22_pruned20 : Secure127 (.pruned (h := 22) (b := 20) (N := 21_760_000)) := Lifetimes.h22_pruned20_bits
/-- Pruned key, kept subtree of height 14: 405,300 signatures. -/
theorem h22_pruned14 : Secure127 (.pruned (h := 22) (b := 14) (N := 405_300)) := Lifetimes.h22_pruned14_bits
/-- Pruned key, kept subtree of height 13: 208,500 signatures. -/
theorem h22_pruned13 : Secure127 (.pruned (h := 22) (b := 13) (N := 208_500)) := Lifetimes.h22_pruned13_bits
/-- Pruned key, kept subtree of height 12: 107,200 signatures. -/
theorem h22_pruned12 : Secure127 (.pruned (h := 22) (b := 12) (N := 107_200)) := Lifetimes.h22_pruned12_bits
/-- Pruned key, kept subtree of height 10: 28,410 signatures. -/
theorem h22_pruned10 : Secure127 (.pruned (h := 22) (b := 10) (N := 28_410)) := Lifetimes.h22_pruned10_bits
/-- Pruned key, kept subtree of height 8: 7,514 signatures. -/
theorem h22_pruned8 : Secure127 (.pruned (h := 22) (b := 8) (N := 7_514)) := Lifetimes.h22_pruned8_bits

/-! ## h = 24 (layered: 10 + 7 + 7, with 8, 6 or 7 coordinates) -/

/-- Full key: 336,700,000 signatures. -/
theorem h24_full : Secure127 (.pruned (h := 24) (b := 24) (N := 336_700_000)) := Lifetimes.h24_full_bits
/-- Pruned key, kept subtree of height 20: 23,830,000 signatures. -/
theorem h24_pruned20 : Secure127 (.pruned (h := 24) (b := 20) (N := 23_830_000)) := Lifetimes.h24_pruned20_bits
/-- Pruned key, kept subtree of height 14: 441,500 signatures. -/
theorem h24_pruned14 : Secure127 (.pruned (h := 24) (b := 14) (N := 441_500)) := Lifetimes.h24_pruned14_bits
/-- Pruned key, kept subtree of height 13: 226,800 signatures. -/
theorem h24_pruned13 : Secure127 (.pruned (h := 24) (b := 13) (N := 226_800)) := Lifetimes.h24_pruned13_bits
/-- Pruned key, kept subtree of height 12: 116,600 signatures. -/
theorem h24_pruned12 : Secure127 (.pruned (h := 24) (b := 12) (N := 116_600)) := Lifetimes.h24_pruned12_bits
/-- Pruned key, kept subtree of height 10: 30,810 signatures. -/
theorem h24_pruned10 : Secure127 (.pruned (h := 24) (b := 10) (N := 30_810)) := Lifetimes.h24_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,154 signatures. -/
theorem h24_pruned8 : Secure127 (.pruned (h := 24) (b := 8) (N := 8_154)) := Lifetimes.h24_pruned8_bits
/-- Layered key, 10 + 7 + 7: 336,700,000 signatures. -/
theorem h24_layered : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (N := 336_700_000)) := Lifetimes.h24_layered_bits
/-- Layered key, 10 + 7 + 7, 6 coordinates (the uniform key of the `2^24` lifetime): 26,670,000 signatures. -/
theorem h24_layered_t6 : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (T := 6) (N := 26_670_000)) :=
  Lifetimes.h24_layered_t6_bits
/-- Layered key, 10 + 7 + 7, 7 coordinates (the uniform key of the `2^26` lifetime): 144,300,000 signatures. -/
theorem h24_layered_t7 : Secure127 (.layered (h := 24) (d := 3) (ℓ := 7) (T := 7) (N := 144_300_000)) :=
  Lifetimes.h24_layered_t7_bits

/-! ## h = 26 (layered: 10 + 8 + 8) -/

/-- Full key: 1,381,000,000 signatures. -/
theorem h26_full : Secure127 (.pruned (h := 26) (b := 26) (N := 1_381_000_000)) := Lifetimes.h26_full_bits
/-- Pruned key, kept subtree of height 20: 26,030,000 signatures. -/
theorem h26_pruned20 : Secure127 (.pruned (h := 26) (b := 20) (N := 26_030_000)) := Lifetimes.h26_pruned20_bits
/-- Pruned key, kept subtree of height 14: 480,100 signatures. -/
theorem h26_pruned14 : Secure127 (.pruned (h := 26) (b := 14) (N := 480_100)) := Lifetimes.h26_pruned14_bits
/-- Pruned key, kept subtree of height 13: 246,900 signatures. -/
theorem h26_pruned13 : Secure127 (.pruned (h := 26) (b := 13) (N := 246_900)) := Lifetimes.h26_pruned13_bits
/-- Pruned key, kept subtree of height 12: 126,900 signatures. -/
theorem h26_pruned12 : Secure127 (.pruned (h := 26) (b := 12) (N := 126_900)) := Lifetimes.h26_pruned12_bits
/-- Pruned key, kept subtree of height 10: 33,480 signatures. -/
theorem h26_pruned10 : Secure127 (.pruned (h := 26) (b := 10) (N := 33_480)) := Lifetimes.h26_pruned10_bits
/-- Pruned key, kept subtree of height 8: 8,830 signatures. -/
theorem h26_pruned8 : Secure127 (.pruned (h := 26) (b := 8) (N := 8_830)) := Lifetimes.h26_pruned8_bits
/-- Layered key, 10 + 8 + 8: 1,381,000,000 signatures. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (N := 1_381_000_000)) := Lifetimes.h26_layered_bits

/-! ## h = 28 (layered: 10 + 9 + 9) -/

/-- Full key: 5,634,000,000 signatures. -/
theorem h28_full : Secure127 (.pruned (h := 28) (b := 28) (N := 5_634_000_000)) := Lifetimes.h28_full_bits
/-- Pruned key, kept subtree of height 20: 28,350,000 signatures. -/
theorem h28_pruned20 : Secure127 (.pruned (h := 28) (b := 20) (N := 28_350_000)) := Lifetimes.h28_pruned20_bits
/-- Pruned key, kept subtree of height 14: 522,000 signatures. -/
theorem h28_pruned14 : Secure127 (.pruned (h := 28) (b := 14) (N := 522_000)) := Lifetimes.h28_pruned14_bits
/-- Pruned key, kept subtree of height 13: 267,900 signatures. -/
theorem h28_pruned13 : Secure127 (.pruned (h := 28) (b := 13) (N := 267_900)) := Lifetimes.h28_pruned13_bits
/-- Pruned key, kept subtree of height 12: 137,400 signatures. -/
theorem h28_pruned12 : Secure127 (.pruned (h := 28) (b := 12) (N := 137_400)) := Lifetimes.h28_pruned12_bits
/-- Pruned key, kept subtree of height 10: 36,190 signatures. -/
theorem h28_pruned10 : Secure127 (.pruned (h := 28) (b := 10) (N := 36_190)) := Lifetimes.h28_pruned10_bits
/-- Pruned key, kept subtree of height 8: 9,541 signatures. -/
theorem h28_pruned8 : Secure127 (.pruned (h := 28) (b := 8) (N := 9_541)) := Lifetimes.h28_pruned8_bits
/-- Layered key, 10 + 9 + 9: 5,634,000,000 signatures. -/
theorem h28_layered : Secure127 (.layered (h := 28) (d := 3) (ℓ := 9) (N := 5_634_000_000)) := Lifetimes.h28_layered_bits

/-! ## All together -/

/-- The 39 configurations above. -/
def configurations : List Params := [
  .pruned 20 20 19_830_000, .pruned 20 14 371_400, .pruned 20 13 191_200, .pruned 20 12 98_480,
  .pruned 20 10 26_080, .pruned 20 8 6_926,
  .pruned 22 22 81_860_000, .pruned 22 20 21_760_000, .pruned 22 14 405_300, .pruned 22 13 208_500,
  .pruned 22 12 107_200, .pruned 22 10 28_410, .pruned 22 8 7_514,
  .pruned 24 24 336_700_000, .pruned 24 20 23_830_000, .pruned 24 14 441_500, .pruned 24 13 226_800,
  .pruned 24 12 116_600, .pruned 24 10 30_810, .pruned 24 8 8_154, .layered 24 3 7 336_700_000,
  .layered 24 3 7 26_670_000 6, .layered 24 3 7 144_300_000 7,
  .pruned 26 26 1_381_000_000, .pruned 26 20 26_030_000, .pruned 26 14 480_100, .pruned 26 13 246_900,
  .pruned 26 12 126_900, .pruned 26 10 33_480, .pruned 26 8 8_830, .layered 26 3 8 1_381_000_000,
  .pruned 28 28 5_634_000_000, .pruned 28 20 28_350_000, .pruned 28 14 522_000, .pruned 28 13 267_900,
  .pruned 28 12 137_400, .pruned 28 10 36_190, .pruned 28 8 9_541, .layered 28 3 9 5_634_000_000]

/-- **Main theorem**: every configuration has 127 bits of SUF-CMA security. -/
theorem requestedSecurity : ∀ P ∈ configurations, Secure127 P := by
  simp only [configurations, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨h20_full, h20_pruned14, h20_pruned13, h20_pruned12, h20_pruned10, h20_pruned8,
    h22_full, h22_pruned20, h22_pruned14, h22_pruned13, h22_pruned12, h22_pruned10, h22_pruned8,
    h24_full, h24_pruned20, h24_pruned14, h24_pruned13, h24_pruned12, h24_pruned10,
    h24_pruned8, h24_layered, h24_layered_t6, h24_layered_t7, h26_full, h26_pruned20, h26_pruned14,
    h26_pruned13, h26_pruned12, h26_pruned10, h26_pruned8, h26_layered, h28_full, h28_pruned20,
    h28_pruned14, h28_pruned13, h28_pruned12, h28_pruned10, h28_pruned8, h28_layered⟩

/-- `Secure127` is the target `SecurityBits P 127` of `Statement.lean`, spelled out. -/
theorem secure127_iff (P : Params) : Secure127 P ↔ SecurityBits P 127 := Iff.rfl


/-! ## 100 bits

The same game at a lower target: `Secure100 P` bounds the forgery probability by `q / 2^100`. Such a
target constrains only the budgets `q < 2^100`, which the small route alone covers
(`ForestPotential.det_bitsS`, `Certificates/ClosingBits.lean`), so these limits are within 0.1% of the
cover attack at 100 bits, the signature count at which a digest query covers a forest instance with
probability `2^-100`. -/

/-- **The claim at 100 bits**, for the scheme with parameters `P`: every adversary whose runs of the
SUF-CMA game make at most `q ≥ 1` hash queries in total forges with probability at most `q / 2^100`. -/
def Secure100 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 100 : ℕ) : ℝ≥0∞)

/-- `Secure100` is the target `SecurityBits P 100` of `Statement.lean`, spelled out. -/
theorem secure100_iff (P : Params) : Secure100 P ↔ SecurityBits P 100 := Iff.rfl

/-! ### h = 20, 100 bits -/

/-- Full key: 59,850,000 signatures at 100 bits. -/
theorem h20_full_100 : Secure100 (.pruned (h := 20) (b := 20) (N := 59_850_000)) := Lifetimes.h20_full_bits100
/-- Pruned key, kept subtree of height 14: 1,135,000 signatures at 100 bits. -/
theorem h20_pruned14_100 : Secure100 (.pruned (h := 20) (b := 14) (N := 1_135_000)) := Lifetimes.h20_pruned14_bits100
/-- Pruned key, kept subtree of height 13: 585,900 signatures at 100 bits. -/
theorem h20_pruned13_100 : Secure100 (.pruned (h := 20) (b := 13) (N := 585_900)) := Lifetimes.h20_pruned13_bits100
/-- Pruned key, kept subtree of height 12: 302,300 signatures at 100 bits. -/
theorem h20_pruned12_100 : Secure100 (.pruned (h := 20) (b := 12) (N := 302_300)) := Lifetimes.h20_pruned12_bits100
/-- Pruned key, kept subtree of height 10: 80,480 signatures at 100 bits. -/
theorem h20_pruned10_100 : Secure100 (.pruned (h := 20) (b := 10) (N := 80_480)) := Lifetimes.h20_pruned10_bits100
/-- Pruned key, kept subtree of height 8: 21,410 signatures at 100 bits. -/
theorem h20_pruned8_100 : Secure100 (.pruned (h := 20) (b := 8) (N := 21_410)) := Lifetimes.h20_pruned8_bits100
/-! ### h = 22, 100 bits -/

/-- Full key: 239,400,000 signatures at 100 bits. -/
theorem h22_full_100 : Secure100 (.pruned (h := 22) (b := 22) (N := 239_400_000)) := Lifetimes.h22_full_bits100
/-- Pruned key, kept subtree of height 20: 63,890,000 signatures at 100 bits. -/
theorem h22_pruned20_100 : Secure100 (.pruned (h := 22) (b := 20) (N := 63_890_000)) := Lifetimes.h22_pruned20_bits100
/-- Pruned key, kept subtree of height 14: 1,209,000 signatures at 100 bits. -/
theorem h22_pruned14_100 : Secure100 (.pruned (h := 22) (b := 14) (N := 1_209_000)) := Lifetimes.h22_pruned14_bits100
/-- Pruned key, kept subtree of height 13: 624,000 signatures at 100 bits. -/
theorem h22_pruned13_100 : Secure100 (.pruned (h := 22) (b := 13) (N := 624_000)) := Lifetimes.h22_pruned13_bits100
/-- Pruned key, kept subtree of height 12: 321,900 signatures at 100 bits. -/
theorem h22_pruned12_100 : Secure100 (.pruned (h := 22) (b := 12) (N := 321_900)) := Lifetimes.h22_pruned12_bits100
/-- Pruned key, kept subtree of height 10: 85,650 signatures at 100 bits. -/
theorem h22_pruned10_100 : Secure100 (.pruned (h := 22) (b := 10) (N := 85_650)) := Lifetimes.h22_pruned10_bits100
/-- Pruned key, kept subtree of height 8: 22,770 signatures at 100 bits. -/
theorem h22_pruned8_100 : Secure100 (.pruned (h := 22) (b := 8) (N := 22_770)) := Lifetimes.h22_pruned8_bits100
/-! ### h = 24, 100 bits -/

/-- Full key: 957,700,000 signatures at 100 bits. -/
theorem h24_full_100 : Secure100 (.pruned (h := 24) (b := 24) (N := 957_700_000)) := Lifetimes.h24_full_bits100
/-- Pruned key, kept subtree of height 20: 68,150,000 signatures at 100 bits. -/
theorem h24_pruned20_100 : Secure100 (.pruned (h := 24) (b := 20) (N := 68_150_000)) := Lifetimes.h24_pruned20_bits100
/-- Pruned key, kept subtree of height 14: 1,287,000 signatures at 100 bits. -/
theorem h24_pruned14_100 : Secure100 (.pruned (h := 24) (b := 14) (N := 1_287_000)) := Lifetimes.h24_pruned14_bits100
/-- Pruned key, kept subtree of height 13: 664,200 signatures at 100 bits. -/
theorem h24_pruned13_100 : Secure100 (.pruned (h := 24) (b := 13) (N := 664_200)) := Lifetimes.h24_pruned13_bits100
/-- Pruned key, kept subtree of height 12: 342,600 signatures at 100 bits. -/
theorem h24_pruned12_100 : Secure100 (.pruned (h := 24) (b := 12) (N := 342_600)) := Lifetimes.h24_pruned12_bits100
/-- Pruned key, kept subtree of height 10: 91,100 signatures at 100 bits. -/
theorem h24_pruned10_100 : Secure100 (.pruned (h := 24) (b := 10) (N := 91_100)) := Lifetimes.h24_pruned10_bits100
/-- Pruned key, kept subtree of height 8: 24,210 signatures at 100 bits. -/
theorem h24_pruned8_100 : Secure100 (.pruned (h := 24) (b := 8) (N := 24_210)) := Lifetimes.h24_pruned8_bits100
/-- Layered key, 10 + 7 + 7: 957,700,000 signatures at 100 bits. -/
theorem h24_layered_100 : Secure100 (.layered (h := 24) (d := 3) (ℓ := 7) (N := 957_700_000)) :=
  Lifetimes.h24_layered_bits100
/-- Layered key, 10 + 7 + 7, 6 coordinates (the uniform key of the `2^24` lifetime): 303,300,000 signatures at 100 bits. -/
theorem h24_layered_t6_100 : Secure100 (.layered (h := 24) (d := 3) (ℓ := 7) (T := 6) (N := 303_300_000)) :=
  Lifetimes.h24_layered_t6_bits100
/-- Layered key, 10 + 7 + 7, 7 coordinates (the uniform key of the `2^26` lifetime): 603,400,000 signatures at 100 bits. -/
theorem h24_layered_t7_100 : Secure100 (.layered (h := 24) (d := 3) (ℓ := 7) (T := 7) (N := 603_400_000)) :=
  Lifetimes.h24_layered_t7_bits100
/-! ### h = 26, 100 bits -/

/-- Full key: 3,830,000,000 signatures at 100 bits. -/
theorem h26_full_100 : Secure100 (.pruned (h := 26) (b := 26) (N := 3_830_000_000)) := Lifetimes.h26_full_bits100
/-- Pruned key, kept subtree of height 20: 72,650,000 signatures at 100 bits. -/
theorem h26_pruned20_100 : Secure100 (.pruned (h := 26) (b := 20) (N := 72_650_000)) := Lifetimes.h26_pruned20_bits100
/-- Pruned key, kept subtree of height 14: 1,370,000 signatures at 100 bits. -/
theorem h26_pruned14_100 : Secure100 (.pruned (h := 26) (b := 14) (N := 1_370_000)) := Lifetimes.h26_pruned14_bits100
/-- Pruned key, kept subtree of height 13: 706,700 signatures at 100 bits. -/
theorem h26_pruned13_100 : Secure100 (.pruned (h := 26) (b := 13) (N := 706_700)) := Lifetimes.h26_pruned13_bits100
/-- Pruned key, kept subtree of height 12: 364,400 signatures at 100 bits. -/
theorem h26_pruned12_100 : Secure100 (.pruned (h := 26) (b := 12) (N := 364_400)) := Lifetimes.h26_pruned12_bits100
/-- Pruned key, kept subtree of height 10: 96,860 signatures at 100 bits. -/
theorem h26_pruned10_100 : Secure100 (.pruned (h := 26) (b := 10) (N := 96_860)) := Lifetimes.h26_pruned10_bits100
/-- Pruned key, kept subtree of height 8: 25,730 signatures at 100 bits. -/
theorem h26_pruned8_100 : Secure100 (.pruned (h := 26) (b := 8) (N := 25_730)) := Lifetimes.h26_pruned8_bits100
/-- Layered key, 10 + 8 + 8: 3,830,000,000 signatures at 100 bits. -/
theorem h26_layered_100 : Secure100 (.layered (h := 26) (d := 3) (ℓ := 8) (N := 3_830_000_000)) :=
  Lifetimes.h26_layered_bits100
/-! ### h = 28, 100 bits -/

/-- Full key: 15,320,000,000 signatures at 100 bits. -/
theorem h28_full_100 : Secure100 (.pruned (h := 28) (b := 28) (N := 15_320_000_000)) := Lifetimes.h28_full_bits100
/-- Pruned key, kept subtree of height 20: 77,400,000 signatures at 100 bits. -/
theorem h28_pruned20_100 : Secure100 (.pruned (h := 28) (b := 20) (N := 77_400_000)) := Lifetimes.h28_pruned20_bits100
/-- Pruned key, kept subtree of height 14: 1,457,000 signatures at 100 bits. -/
theorem h28_pruned14_100 : Secure100 (.pruned (h := 28) (b := 14) (N := 1_457_000)) := Lifetimes.h28_pruned14_bits100
/-- Pruned key, kept subtree of height 13: 751,500 signatures at 100 bits. -/
theorem h28_pruned13_100 : Secure100 (.pruned (h := 28) (b := 13) (N := 751_500)) := Lifetimes.h28_pruned13_bits100
/-- Pruned key, kept subtree of height 12: 387,400 signatures at 100 bits. -/
theorem h28_pruned12_100 : Secure100 (.pruned (h := 28) (b := 12) (N := 387_400)) := Lifetimes.h28_pruned12_bits100
/-- Pruned key, kept subtree of height 10: 102,900 signatures at 100 bits. -/
theorem h28_pruned10_100 : Secure100 (.pruned (h := 28) (b := 10) (N := 102_900)) := Lifetimes.h28_pruned10_bits100
/-- Pruned key, kept subtree of height 8: 27,340 signatures at 100 bits. -/
theorem h28_pruned8_100 : Secure100 (.pruned (h := 28) (b := 8) (N := 27_340)) := Lifetimes.h28_pruned8_bits100
/-- Layered key, 10 + 9 + 9: 15,320,000,000 signatures at 100 bits. -/
theorem h28_layered_100 : Secure100 (.layered (h := 28) (d := 3) (ℓ := 9) (N := 15_320_000_000)) :=
  Lifetimes.h28_layered_bits100

/-- The 39 configurations at 100 bits. -/
def configurations100 : List Params := [
  .pruned 20 20 59_850_000, .pruned 20 14 1_135_000, .pruned 20 13 585_900, .pruned 20 12 302_300,
  .pruned 20 10 80_480, .pruned 20 8 21_410, .pruned 22 22 239_400_000, .pruned 22 20 63_890_000,
  .pruned 22 14 1_209_000, .pruned 22 13 624_000, .pruned 22 12 321_900, .pruned 22 10 85_650,
  .pruned 22 8 22_770, .pruned 24 24 957_700_000, .pruned 24 20 68_150_000, .pruned 24 14 1_287_000,
  .pruned 24 13 664_200, .pruned 24 12 342_600, .pruned 24 10 91_100, .pruned 24 8 24_210,
  .layered 24 3 7 957_700_000, .layered 24 3 7 303_300_000 6, .layered 24 3 7 603_400_000 7,
  .pruned 26 26 3_830_000_000, .pruned 26 20 72_650_000, .pruned 26 14 1_370_000, .pruned 26 13 706_700,
  .pruned 26 12 364_400, .pruned 26 10 96_860, .pruned 26 8 25_730, .layered 26 3 8 3_830_000_000,
  .pruned 28 28 15_320_000_000, .pruned 28 20 77_400_000, .pruned 28 14 1_457_000, .pruned 28 13 751_500,
  .pruned 28 12 387_400, .pruned 28 10 102_900, .pruned 28 8 27_340, .layered 28 3 9 15_320_000_000]

/-- **Main theorem at 100 bits**: every configuration has 100 bits of SUF-CMA security. -/
theorem requestedSecurity100 : ∀ P ∈ configurations100, Secure100 P := by
  simp only [configurations100, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨h20_full_100, h20_pruned14_100, h20_pruned13_100, h20_pruned12_100, h20_pruned10_100,
    h20_pruned8_100, h22_full_100, h22_pruned20_100, h22_pruned14_100, h22_pruned13_100, h22_pruned12_100,
    h22_pruned10_100, h22_pruned8_100, h24_full_100, h24_pruned20_100, h24_pruned14_100, h24_pruned13_100,
    h24_pruned12_100, h24_pruned10_100, h24_pruned8_100, h24_layered_100, h24_layered_t6_100,
    h24_layered_t7_100, h26_full_100, h26_pruned20_100, h26_pruned14_100, h26_pruned13_100, h26_pruned12_100,
    h26_pruned10_100, h26_pruned8_100, h26_layered_100, h28_full_100, h28_pruned20_100, h28_pruned14_100,
    h28_pruned13_100, h28_pruned12_100, h28_pruned10_100, h28_pruned8_100, h28_layered_100⟩

end LeanForest
