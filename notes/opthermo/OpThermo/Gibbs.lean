import OpThermo.Accessibility

/-!
# Gibbs 自由エネルギー：一定温度・一定圧力の環境でのエントロピー原理

系 `X` を環境 (溜め) `R` と接触させ、全体を外界から孤立させる。
全体のエネルギー `U` と体積 `V` は保存し、質量も保存する。

## 主結果

* `gibbs_criterion` (理想的な溜め)：溜めのエントロピーが `U`, `V` の一次式
  `σ + (U + p₀ V)/T₀` で書けるなら、
  `X + R ≺ Y + R' ↔ G Y ≤ G X` (`G = U + p₀ V - T₀ S`)。
  証明は `Entropy.lean` のエントロピー原理と加法性だけを使う。
* `total_entropy_ideal`：同じ仮定で `ΔS_全体 = -ΔG / T₀` (等式)。
* `large_reservoir_limit`：有限の溜めでも、示量性 `S(λ x) = λ s(x)` と `s` の微分可能性から、
  溜めを大きくする極限で `ΔS_全体 → -ΔG / T₀`。`T₀ = 1/(∂s/∂u)`, `p₀ = T₀ ∂s/∂v`。
  「溜めが十分大きいので `T₀, p₀` は変わらない」という議論の正確な形である。
* `large_reservoir_criterion`：`G` が厳密に減るなら十分大きな溜めで到達可能、
  厳密に増えるなら十分大きな溜めで到達不可能。等号の場合はこの極限からは決まらない。
* `gibbs_hasDerivAt`：`dU = T dS - p dV` の下で `dG = -S dT + V dp`。

## 第一法則とのつなぎ

`gibbs_criterion` の `U` は任意の関数である。
`isolated_process_lowers_gibbs` と `reachable_of_gibbs_le` では、断熱到達性を断熱操作の存在とし
(`CompositeOps.toAdiabatic`)、`U` を断熱仕事から作った示量的な内部エネルギー
(`CompositeOps.energy`) とする。追加の仮定は要らない。
-/

open NNReal Filter Topology

namespace OpThermo

/-- `T₀, p₀` の環境に対する Gibbs 関数 `G = U + p₀ V - T₀ S`。 -/
def gibbs {Γ : Type*} (S U V : Γ → ℝ) (T₀ p₀ : ℝ) (X : Γ) : ℝ :=
  U X + p₀ * V X - T₀ * S X

/-- 理想的な溜めでは、全エントロピー変化は `-ΔG / T₀` に等しい。 -/
theorem total_entropy_ideal {Γ : Type*} (S U V : Γ → ℝ) {T₀ p₀ σ : ℝ} (hT : T₀ ≠ 0)
    {X Y : Γ} {UR VR UR' VR' : ℝ}
    (hU : U X + UR = U Y + UR') (hV : V X + VR = V Y + VR') :
    (S Y + (σ + (UR' + p₀ * VR') / T₀)) - (S X + (σ + (UR + p₀ * VR) / T₀)) =
      -(gibbs S U V T₀ p₀ Y - gibbs S U V T₀ p₀ X) / T₀ := by
  obtain rfl : UR' = U X + UR - U Y := by linarith
  obtain rfl : VR' = V X + VR - V Y := by linarith
  unfold gibbs
  field_simp
  ring

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **Gibbs 自由エネルギーの最小原理** (理想的な溜め)。

仮定：
* `hmass`：組成の保存。
* `hU`, `hV`：系と溜めを合わせたエネルギーと体積の保存 (外界とは仕事も交換しない)。
* `hR`, `hR'`：溜めのエントロピーは `U`, `V` の一次式で、傾きは `1/T₀` と `p₀/T₀`。

結論：系と溜めの複合状態 `X + R` から `Y + R'` へ断熱到達できることと、
`G_{T₀,p₀}` が増えないことは同値。 -/
theorem gibbs_criterion (c : Calibration 𝒮 C) (U V : 𝒮 → ℝ) {T₀ p₀ σ : ℝ} (hT : 0 < T₀)
    {X Y R R' : 𝒮} (hmass : comp (X + R) = comp (Y + R'))
    (hU : U X + U R = U Y + U R') (hV : V X + V R = V Y + V R')
    (hR : c.entropy R = σ + (U R + p₀ * V R) / T₀)
    (hR' : c.entropy R' = σ + (U R' + p₀ * V R') / T₀) :
    X + R ≺ Y + R' ↔ gibbs c.entropy U V T₀ p₀ Y ≤ gibbs c.entropy U V T₀ p₀ X := by
  rw [Calibration.entropy_principle hmass, Calibration.entropy_add, Calibration.entropy_add,
    ← sub_nonneg, hR, hR', total_entropy_ideal c.entropy U V hT.ne' hU hV,
    neg_div, neg_nonneg, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hT.le⟩

end Adiabatic

namespace CompositeOps

variable {𝒮 C W : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] (O : CompositeOps 𝒮 C W)
  {m : W → ℝ} (hpi : O.PathIndependent m) (ref : (C → ℝ≥0) →ₗ[ℝ≥0] 𝒮)
  (href : ∀ k, O.comp (ref k) = k)

include hpi

/-- 孤立した断熱操作 (重りの正味の仕事が `0`) で `X + R` から `Y + R'` に移れるなら、
`G_{T₀,p₀}` は増えない。断熱到達性は断熱操作の存在、`U` は断熱仕事から作った示量的な
内部エネルギー (`CompositeOps.energy`)。 -/
theorem isolated_process_lowers_gibbs (c : O.Calibration)
    (V : 𝒮 → ℝ) {T₀ p₀ σ : ℝ} (hT : 0 < T₀) {X Y R R' : 𝒮}
    (hV : V X + V R = V Y + V R')
    (hR : O.entropy c R = σ + (O.energy ref href m R + p₀ * V R) / T₀)
    (hR' : O.entropy c R' = σ + (O.energy ref href m R' + p₀ * V R') / T₀)
    (p : O.Operation (X + R) (Y + R')) (hp : O.work m p = 0) :
    gibbs (O.entropy c) (O.energy ref href m) V T₀ p₀ Y ≤
      gibbs (O.entropy c) (O.energy ref href m) V T₀ p₀ X := by
  have h := O.energy_spec ref href hpi p
  rw [hp, O.energy_add ref href hpi, O.energy_add ref href hpi] at h
  exact (@Adiabatic.gibbs_criterion 𝒮 C _ _ O.toAdiabatic c _ V T₀ p₀ σ hT X Y R R'
    (O.comp_eq p) (by linarith) hV hR hR').1 ⟨p⟩

/-- 逆向き：組成、エネルギー、体積が保存する終状態で `G_{T₀,p₀}` が増えないなら、
`X + R` から `Y + R'` への断熱操作が存在し、その仕事は `0` である。 -/
theorem reachable_of_gibbs_le (c : O.Calibration)
    (V : 𝒮 → ℝ) {T₀ p₀ σ : ℝ} (hT : 0 < T₀) {X Y R R' : 𝒮}
    (hmass : O.comp (X + R) = O.comp (Y + R'))
    (hUc : O.energy ref href m X + O.energy ref href m R =
      O.energy ref href m Y + O.energy ref href m R')
    (hV : V X + V R = V Y + V R')
    (hR : O.entropy c R = σ + (O.energy ref href m R + p₀ * V R) / T₀)
    (hR' : O.entropy c R' = σ + (O.energy ref href m R' + p₀ * V R') / T₀)
    (hG : gibbs (O.entropy c) (O.energy ref href m) V T₀ p₀ Y ≤
      gibbs (O.entropy c) (O.energy ref href m) V T₀ p₀ X) :
    ∃ p : O.Operation (X + R) (Y + R'), O.work m p = 0 := by
  obtain ⟨p⟩ := (@Adiabatic.gibbs_criterion 𝒮 C _ _ O.toAdiabatic c _ V T₀ p₀ σ hT X Y R R'
    hmass hUc hV hR hR').2 hG
  refine ⟨p, ?_⟩
  have h := O.energy_spec ref href hpi p
  rw [O.energy_add ref href hpi, O.energy_add ref href hpi] at h
  linarith

end CompositeOps

/-- 大きさ `λ` の溜めのエントロピー変化の極限。`s` が `x₀` で微分可能なら
`λ (s (x₀ + λ⁻¹ Δ) - s x₀) → s' Δ`。 -/
theorem large_reservoir_limit {s : ℝ × ℝ → ℝ} {s' : ℝ × ℝ →L[ℝ] ℝ} {x₀ : ℝ × ℝ}
    (hs : HasFDerivAt s s' x₀) (Δ : ℝ × ℝ) :
    Tendsto (fun lam : ℝ => lam * (s (x₀ + lam⁻¹ • Δ) - s x₀)) atTop (𝓝 (s' Δ)) := by
  simpa using hs.lim Δ (c := id) (l := atTop) (by simpa using tendsto_abs_atTop_atTop)

/-- **大きな溜めのエントロピー**：示量性 `SR λ (λ x) = λ s(x)` と `s` の微分可能性があれば、
大きさ `λ` の溜めのエネルギーと体積を `(ΔU, ΔV)` だけ変えたときのエントロピー変化は、
`λ → ∞` で `(ΔU + p₀ ΔV) / T₀` に近づく。ここで `T₀ := 1/β`, `p₀ := (∂s/∂v)/β`,
`β := ∂s/∂u`。理想的な溜めの一次式は、この極限である。 -/
theorem large_reservoir_entropy {SR : ℝ → ℝ × ℝ → ℝ}
    {s : ℝ × ℝ → ℝ} {s' : ℝ × ℝ →L[ℝ] ℝ} {x₀ : ℝ × ℝ}
    (hext : ∀ lam > 0, ∀ x, SR lam (lam • x) = lam * s x)
    (hs : HasFDerivAt s s' x₀) (hβ : s' (1, 0) ≠ 0) (ΔU ΔV : ℝ) :
    Tendsto (fun lam : ℝ => SR lam (lam • x₀ + (ΔU, ΔV)) - SR lam (lam • x₀)) atTop
      (𝓝 ((ΔU + s' (0, 1) / s' (1, 0) * ΔV) / (s' (1, 0))⁻¹)) := by
  have hval : s' (ΔU, ΔV) = (ΔU + s' (0, 1) / s' (1, 0) * ΔV) / (s' (1, 0))⁻¹ := by
    have hΔ : ((ΔU, ΔV) : ℝ × ℝ) = ΔU • ((1 : ℝ), (0 : ℝ)) + ΔV • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hΔ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [← hval]
  refine (large_reservoir_limit hs (ΔU, ΔV)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have h1 : lam • x₀ + (ΔU, ΔV) = lam • (x₀ + lam⁻¹ • (ΔU, ΔV)) := by
    rw [smul_add, smul_inv_smul₀ hlam.ne']
  rw [h1, hext lam hlam, hext lam hlam]
  ring

/-- 大きさ `λ` の溜めを使ったときの全エントロピー変化。溜めの状態は `(U, V)` で表し、
始めは `λ x₀`。系が `X → Y` と変わると、溜めは `(-ΔU, -ΔV)` だけ変わる。 -/
def totalEntropyChange {Γ : Type*} (S U V : Γ → ℝ) (SR : ℝ → ℝ × ℝ → ℝ) (x₀ : ℝ × ℝ)
    (X Y : Γ) (lam : ℝ) : ℝ :=
  S Y - S X + (SR lam (lam • x₀ + (-(U Y - U X), -(V Y - V X))) - SR lam (lam • x₀))

/-- **大きな溜めの極限での Gibbs 関数**。

仮定：
* `hext`：示量性 `SR λ (λ x) = λ s(x)` (`Entropy.lean` の `entropy_smul` にあたる)。
* `hs`：単位量あたりのエントロピー `s(u, v)` が `x₀` で微分可能。
* `hβ`：`β := ∂s/∂u > 0` (正の温度)。

`T₀ := 1/β`, `p₀ := (∂s/∂v)/β` とおくと、`ΔS_全体 → -ΔG_{T₀,p₀} / T₀`。 -/
theorem gibbs_large_reservoir {Γ : Type*} (S U V : Γ → ℝ) {SR : ℝ → ℝ × ℝ → ℝ}
    {s : ℝ × ℝ → ℝ} {s' : ℝ × ℝ →L[ℝ] ℝ} {x₀ : ℝ × ℝ}
    (hext : ∀ lam > 0, ∀ x, SR lam (lam • x) = lam * s x)
    (hs : HasFDerivAt s s' x₀) (hβ : 0 < s' (1, 0)) (X Y : Γ) :
    Tendsto (totalEntropyChange S U V SR x₀ X Y) atTop
      (𝓝 (-(gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y -
        gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X) / (s' (1, 0))⁻¹)) := by
  set Δ : ℝ × ℝ := (-(U Y - U X), -(V Y - V X))
  have hlim := (large_reservoir_limit hs Δ).const_add (S Y - S X)
  have hval : S Y - S X + s' Δ = -(gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y -
      gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X) / (s' (1, 0))⁻¹ := by
    have hΔ : Δ = (-(U Y - U X)) • ((1 : ℝ), (0 : ℝ)) + (-(V Y - V X)) • ((0 : ℝ), (1 : ℝ)) := by
      simp [Δ]
    rw [hΔ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    unfold gibbs
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  unfold totalEntropyChange
  have h1 : lam • x₀ + Δ = lam • (x₀ + lam⁻¹ • Δ) := by
    rw [smul_add, smul_inv_smul₀ hlam.ne']
  rw [h1, hext lam hlam, hext lam hlam]
  ring

/-- **大きな溜めでの判定**：到達可能性がエントロピー原理で決まるとする (`hreach`)。
`G` が厳密に減る変化は十分大きな溜めで到達可能、厳密に増える変化は到達不可能。 -/
theorem large_reservoir_criterion {Γ : Type*} (S U V : Γ → ℝ) {SR : ℝ → ℝ × ℝ → ℝ}
    {s : ℝ × ℝ → ℝ} {s' : ℝ × ℝ →L[ℝ] ℝ} {x₀ : ℝ × ℝ}
    (hext : ∀ lam > 0, ∀ x, SR lam (lam • x) = lam * s x)
    (hs : HasFDerivAt s s' x₀) (hβ : 0 < s' (1, 0)) {X Y : Γ} (reach : ℝ → Prop)
    (hreach : ∀ lam, reach lam ↔ 0 ≤ totalEntropyChange S U V SR x₀ X Y lam) :
    (gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y <
        gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X → ∀ᶠ lam in atTop, reach lam) ∧
    (gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X <
        gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y → ∀ᶠ lam in atTop, ¬ reach lam) := by
  have hlim := gibbs_large_reservoir S U V hext hs hβ X Y
  have hT : 0 < (s' (1, 0))⁻¹ := inv_pos.2 hβ
  constructor
  · intro h
    have hpos : 0 < -(gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y -
        gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X) / (s' (1, 0))⁻¹ :=
      div_pos (by linarith) hT
    filter_upwards [hlim.eventually (lt_mem_nhds hpos)] with lam h
    exact (hreach lam).2 h.le
  · intro h
    have hneg : -(gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) Y -
        gibbs S U V (s' (1, 0))⁻¹ (s' (0, 1) / s' (1, 0)) X) / (s' (1, 0))⁻¹ < 0 :=
      div_neg_of_neg_of_pos (by linarith) hT
    filter_upwards [hlim.eventually (gt_mem_nhds hneg)] with lam h
    rw [hreach lam]
    exact not_le.2 h

/-- **`dG = -S dT + V dp`**：経路に沿って `dU = T dS - p dV` が成り立つとき、
`G = U + p V - T S` の変化率は `-S T' + V p'`。 -/
theorem gibbs_hasDerivAt {U S V T p : ℝ → ℝ} {t U' S' V' T' p' : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (hV : HasDerivAt V V' t)
    (hT : HasDerivAt T T' t) (hp : HasDerivAt p p' t)
    (hfund : U' = T t * S' - p t * V') :
    HasDerivAt (fun t => U t + p t * V t - T t * S t) (-S t * T' + V t * p') t := by
  convert (hU.add (hp.mul hV)).sub (hT.mul hS) using 1
  rw [hfund]; ring

end OpThermo
