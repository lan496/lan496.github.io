import OpThermo.Concavity

/-!
# 熱容量

体積と組成を固定した単純系の状態 `γ u` (内部エネルギー `u`) と、そのエントロピー `s u` を考える。

* `heatCapacity s u := (dT/du)⁻¹`：温度を単位だけ上げるのに要るエネルギー (定積熱容量)。
* `heatCapacity_eq`：`β := s'`, `β' := s''` とすると `C = -β² / β'`。
* `heatCapacity_pos`：`s` が凹 (`Concavity.lean`) で `β' ≠ 0` なら `C > 0`。
* `entropy_hasDerivAt_temperature`：温度の関数として見たエントロピーの変化率は `C / T`。
-/

open Filter Topology Set NNReal

namespace OpThermo

/-- 熱容量 `C := du/dT`。体積と組成を固定した系では定積熱容量 `C_V` である。 -/
noncomputable def heatCapacity (s : ℝ → ℝ) (u : ℝ) : ℝ := (deriv (temperature s) u)⁻¹

/-- 温度 `T = 1/β` の変化率は `-β' / β²`。 -/
theorem temperature_hasDerivAt {s : ℝ → ℝ} {u β' : ℝ} (hβ' : HasDerivAt (deriv s) β' u)
    (hβ : deriv s u ≠ 0) :
    HasDerivAt (temperature s) (-β' / (deriv s u) ^ 2) u := by
  have h := hβ'.inv hβ
  exact h

/-- **熱容量とエントロピーの二階微分**：`β ≠ 0` かつ `β' ≠ 0` なら、温度はエネルギーについて
変化率 `T' = -β'/β² ≠ 0` を持ち、熱容量 `C = 1/T'` は `C · T' = 1` を満たして `C = -β² / β'`。
`β' = 0` のとき `heatCapacity` は Lean の約束 `0⁻¹ = 0` で `0` を返すが、これは熱容量ではない。 -/
theorem heatCapacity_eq {s : ℝ → ℝ} {u β' : ℝ} (hβ' : HasDerivAt (deriv s) β' u)
    (hβ : deriv s u ≠ 0) (hβ'0 : β' ≠ 0) :
    heatCapacity s u * deriv (temperature s) u = 1 ∧
      heatCapacity s u = -(deriv s u) ^ 2 / β' := by
  have hT := (temperature_hasDerivAt hβ' hβ).deriv
  have hT0 : deriv (temperature s) u ≠ 0 := by
    rw [hT]; exact div_ne_zero (neg_ne_zero.2 hβ'0) (pow_ne_zero 2 hβ)
  refine ⟨inv_mul_cancel₀ hT0, ?_⟩
  rw [heatCapacity, hT, inv_div, neg_div, div_neg]

/-- **熱容量は正**：`s` が `u` の近くで凹、`β ≠ 0`、`β' ≠ 0` なら `C > 0`。 -/
theorem heatCapacity_pos {s : ℝ → ℝ} {I : Set ℝ} {u β' : ℝ} (hc : ConcaveOn ℝ I s)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ s x) (hu : I ∈ 𝓝 u)
    (hβ' : HasDerivAt (deriv s) β' u) (hβ'0 : β' ≠ 0) (hβ : deriv s u ≠ 0) :
    0 < heatCapacity s u := by
  have hanti := hc.antitoneOn_deriv hd
  have hle : β' ≤ 0 := by
    have := hanti.derivWithin_nonpos (x := u)
    rwa [derivWithin_of_mem_nhds hu, hβ'.deriv] at this
  have hlt : β' < 0 := lt_of_le_of_ne hle hβ'0
  rw [(heatCapacity_eq hβ' hβ hβ'0).2, neg_div, ← div_neg]
  exact div_pos (by positivity) (neg_pos.2 hlt)

/-- **熱量測定の微分形**：`T` の関数として見たエントロピー `s ∘ u` の変化率は `C / T`。
`u(T)` が `T` で微分可能で、その微分が `C` であるとする。 -/
theorem entropy_hasDerivAt_temperature {s ueq : ℝ → ℝ} {T C : ℝ}
    (hu : HasDerivAt ueq C T) (hs : HasDerivAt s (1 / T) (ueq T)) :
    HasDerivAt (fun T => s (ueq T)) (C / T) T := by
  rw [show C / T = 1 / T * C by ring]
  exact hs.comp T hu

end OpThermo
