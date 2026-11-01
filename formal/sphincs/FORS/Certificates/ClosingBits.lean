import FORS.Certificates.Closing

/-! **Fewer bits from the small route alone.** A target of `bits ≤ 127` bits only constrains the
budgets `q < 2^bits`: above, `q / 2^bits ≥ 1` bounds every probability. So one small-route check at
`qh ≥ 2^bits - 1` covers every budget, with the closed form of `det_smallF` compared with `q / 2^bits`
instead of `q / 2^127`: the rational check `checkSmallS` is `checkSmallF` with the right-hand side
`2^(128 - bits)` in place of `2` (`det_bitsS`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### The closed form against `q / 2^bits` -/

omit [Params] in
/-- The real inequality behind the closed form, at `bits ≤ 127` bits: `small_realFF` with the
right-hand side `2^(128 - bits)` of the check. -/
theorem small_realS (bits : ℕ) (hbits : bits ≤ 127) (x qh q N ρ B c M : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh)
    (hqh : qh ≤ 2 ^ 127) (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (_hB : 0 ≤ B) (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hcheck : ρ + 2 ^ 128 * B + (2 * M - 1) * qh / (M * 2 ^ 129) + qh * c + 1 / 2 ^ 60 ≤ 2 ^ (128 - bits)) :
    ρ * x / 2 ^ 128 + x * B + (2 ^ 128)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (1 / 2) ^ 201 + 2 * (q / 2 ^ 256) ≤
      q / 2 ^ bits := by
  have hM0 : M ≠ 0 := by linarith
  have hr0 : 0 ≤ (2 - 1 / M) / 2 ^ 129 := by
    apply div_nonneg _ (by positivity)
    have : 1 / M ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have e : (2 * M - 1) * qh / (M * 2 ^ 129) = qh * ((2 - 1 / M) / 2 ^ 129) := by
    field_simp
  have e0 : (2 ^ 128 : ℝ)⁻¹ * (x * x / 2 * ((2 - 1 / M) / 2 ^ 128)) =
      x * (2 ^ 128)⁻¹ * (x * ((2 - 1 / M) / 2 ^ 129)) := by
    ring
  have hWb : (2 : ℝ) ^ bits * 2 ^ (128 - bits) = 2 ^ 128 := by
    rw [← pow_add]
    congr 1
    omega
  have hW2 : (2 : ℝ) ≤ 2 ^ (128 - bits) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (128 - bits) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hqb : q / (2 : ℝ) ^ bits = q * 2 ^ (128 - bits) / 2 ^ 128 := by
    rw [← hWb]
    field_simp
  generalize (2 : ℝ) ^ (128 - bits) = W at hcheck hW2 hqb
  rw [e] at hcheck
  rw [e0, hqb]
  generalize (2 - 1 / M) / 2 ^ 129 = r at hr0 hcheck ⊢
  have h1 : x * r ≤ qh * r := mul_le_mul_of_nonneg_right hxq hr0
  have h2 : x * c ≤ qh * c := mul_le_mul_of_nonneg_right hxq hc
  have hbr : ρ + 2 ^ 128 * B + x * r + x * c ≤ W - 1 / 2 ^ 60 := by linarith
  have hmain : ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (x * r) + x * (2 ^ 128)⁻¹ * (x * c) =
      x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) := by
    field_simp
  have hmain' : x * (2 ^ 128)⁻¹ * (ρ + 2 ^ 128 * B + x * r + x * c) ≤
      x * (2 ^ 128)⁻¹ * (W - 1 / 2 ^ 60) := mul_le_mul_of_nonneg_left hbr (by positivity)
  have hfail : ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 ≤ (x + N) * 2 * (1 / 2) ^ 201 := by
    have hx1 : x * (2 ^ 128 : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      linarith
    have : x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ x + N := by
      calc x * (2 ^ 128 : ℝ)⁻¹ * (x + N) ≤ 1 * (x + N) := mul_le_mul_of_nonneg_right hx1 (by positivity)
        _ = x + N := one_mul _
    have hp : (0 : ℝ) ≤ (1 / 2) ^ 201 := by positivity
    nlinarith
  have e201 : ((1 : ℝ) / 2) ^ 201 = 1 / 2 ^ 201 := by rw [div_pow, one_pow]
  rw [hmain]
  rw [e201] at hfail ⊢
  have key : x * (2 ^ 128 : ℝ)⁻¹ * (W - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
      2 * (q / 2 ^ 256) ≤ q * W / 2 ^ 128 := by
    have ex : x * (2 ^ 128 : ℝ)⁻¹ * (W - 1 / 2 ^ 60) + (x + N) * 2 * (1 / 2 ^ 201) + 2 * (1 / 2 ^ 201) +
        2 * (q / 2 ^ 256) = (x * (2 ^ 127 * W - 2 ^ 67) + (x + N) * 2 ^ 55 + 2 ^ 55 + q) / 2 ^ 255 := by
      field_simp
    have ey : q * W / (2 : ℝ) ^ 128 = q * W * 2 ^ 127 / 2 ^ 255 := by
      field_simp
    rw [ex, ey]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hqx : (q - x) * 2 ≤ (q - x) * W := mul_le_mul_of_nonneg_left hW2 (by linarith)
    nlinarith
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The small-budget bound in closed form against `q / 2^bits`.** -/
theorem small_closeS (bits : ℕ) (hbits : bits ≤ 127) (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh)
    (hqh : qh ≤ 2 ^ 127) (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
        qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 ^ (128 - bits)) :
    smallMainFF ρ q B c + smallFailF q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCostF
  have hq'1 : q' + 1 ≤ q := by omega
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hM : (1 : ℝ) ≤ (H0.scanM : ℝ) := by exact_mod_cast H0.scanM_pos
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hreal := small_realS bits hbits (q' : ℝ) qh q signatureLimit ρ B c (H0.scanM : ℝ) (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' hM hcheck
  have hr0 : (0 : ℝ) ≤ (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 := by
    apply div_nonneg _ (by positivity)
    have : 1 / (H0.scanM : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM
    linarith
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hqbits : (q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ bits) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  refine le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_right (lam_start_leF q') 2)) le_rfl) ?_
  have hC : ((Nat.choose q' 2 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((q' : ℝ) * q' / 2) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Nat.cast_choose_two]
    have h0 : (0 : ℝ) ≤ (q' : ℝ) := Nat.cast_nonneg _
    nlinarith
  unfold smallMainFF smallFailF
  rw [← hq'def]
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul' le_rfl (mul_le_mul' hC le_rfl))) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  rw [rateS_eqF, hhalf, hq256, hqbits, ν_eq_ofReal, hnat q', hnat signatureLimit, h2]
  generalize (2 - 1 / (H0.scanM : ℝ)) / 2 ^ 128 = r at hr0 hreal ⊢
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The rational check -/

/-- The rational small-route check at `bits` bits: `checkSmallF` with the right-hand side
`2^(128 - bits)`, for `bits ≤ 127` and a right end `qh ≥ 2^bits - 1` of the small budgets. -/
def checkSmallS (H b a N qh bits : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (bits ≤ 127) && decide (2 ^ bits ≤ qh + 1) &&
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) / (2 ^ b * 2 ^ a) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (2 * (H0.scanMb H b : ℚ) - 1) * (qh : ℚ) / ((H0.scanMb H b : ℚ) * 2 ^ 129) +
      (2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ a)) * qh * c + 1 / 2 ^ 60 ≤
        2 ^ (128 - bits))

omit [Params] in
theorem checkSmallS_sound {H b a N qh bits : ℕ} {ρ cthr B c : ℚ} (h : checkSmallS H b a N qh bits ρ cthr B c = true) :
    bits ≤ 127 ∧ 2 ^ bits ≤ qh + 1 ∧
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (N : ℝ) / (2 ^ b * 2 ^ a) ≤ (ρ : ℝ) - 1 - (qh : ℝ) / 2 ^ 128 ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (2 * (H0.scanMb H b : ℝ) - 1) * (qh : ℝ) / ((H0.scanMb H b : ℝ) * 2 ^ 129) +
        (2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ a)) * qh * (c : ℝ) + 1 / 2 ^ 60 ≤
          2 ^ (128 - bits) := by
  simp only [checkSmallS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have r1 := (Rat.cast_le (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have r4 := (Rat.cast_le (K := ℝ)).mpr h4
  have r5 := (Rat.cast_le (K := ℝ)).mpr h5
  have r8 := (Rat.cast_le (K := ℝ)).mpr h8
  have r11 := (Rat.cast_le (K := ℝ)).mpr h11
  have r12 := (Rat.cast_le (K := ℝ)).mpr h12
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at r1 r2 r3 r4 r5 r8 r11 r12
  exact ⟨hb0, hb1, ⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, r11, r12⟩

/-! ### The deterministic signer at `bits` bits -/

set_option maxRecDepth 100000 in
/-- **`bits` bits for the deterministic signer of the FORS variant, `bits ≤ 127`,** from one small-route
check at a right end `qh ≥ 2^bits - 1` (with a table whose rate is checked at `qh`): every budget
`q < 2^bits` is a small budget, and a larger budget bounds nothing. -/
theorem det_bitsS (hb0 : 0 < keptHeight topLayer) (H b k a N bits : ℕ) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate H b N qh t = true) (ho : H0.checkOpt H b k a t o = true)
    (hon : H0.checkOptN H k a t on = true)
    (hsmall : checkSmallS H b a N qh bits ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true) :
    HasClassicalSecurityBits bits := by
  obtain ⟨hbits, hqh1, hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallS_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set c : ℚ := (2 ^ b * on.En : ℚ) / 2 with hcdef
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ a) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ a) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) / (2 ^ b * 2 ^ a) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by
      rw [hκR]
      linarith
    exact_mod_cast hR
  have hc2 : (0 : ℚ) ≤ κ * c := mul_nonneg hκ0 hc
  have hcheck' : (ρ : ℝ) + 2 ^ 128 * (o.B : ℝ) +
      (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
      qh * ((κ * c : ℚ) : ℝ) + 1 / 2 ^ 60 ≤ 2 ^ (128 - bits) := by
    rw [Rat.cast_mul, hκR, ← H0.scanMb_eq H b hH hb]
    refine le_of_eq_of_le ?_ hcheck
    ring
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ bits ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hqb : q < 2 ^ bits := Nat.lt_of_not_le hbig
  have hpow : 2 ^ bits ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) hbits
  have hs : q - keygenCost ≤ qh := by omega
  have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
  have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
    numeric_monoF hnum hx (by positivity)
  have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ) := by
    have he : (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) =
        (N : ℝ) / (2 ^ b * 2 ^ a) := by
      rw [hb, ha, hN]
      field_simp
    rw [hκR, he]
    linarith
  refine le_trans (det_smallF hb0 adversary q hbound (by omega) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq H b k a N hH hb hk ha hN t o on
    hpt qh hrt hs ho hon hcthr) ?_
  exact small_closeS bits hbits q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'

end FORS.Security.ForsPotential
