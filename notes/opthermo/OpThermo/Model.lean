import OpThermo.Entropy

/-!
# 公理系の無矛盾性：具体的なモデル

`Adiabatic` の公理と基準状態 `X₀ ≺≺ X₁` が同時に満たされる例を作る。
公理系が矛盾していれば、どんな定理も証明できてしまう。モデルがあれば、
`Entropy.lean` の定理が空虚でないことが保証される。

成分は一つ (`Unit`)、状態は (質量, エントロピー) の組 `ℝ≥0 × ℝ≥0`、到達性は
「質量が等しく、第二成分が減らない」とする。組成の違う状態の間はどちら向きにも移れない。
このモデルでは、構成したエントロピーが第二成分と一致する (`model_entropy`)。

同じモデルは、近傍を使う Carathéodory の原理 (どの状態のどの近くにも断熱的に到達できない
状態がある) が公理から出ないことも示す。`X₀ = (1, 0)` からは、質量が同じすべての状態に
断熱的に移れる (`model_reach_all`)。
-/

open NNReal Filter Topology

namespace OpThermo

/-- モデルの状態：(質量, エントロピー) -/
abbrev ModelState := ℝ≥0 × ℝ≥0

noncomputable instance : Adiabatic ModelState Unit where
  prec X Y := X.1 = Y.1 ∧ (X.2 : ℝ) ≤ Y.2
  refl X := ⟨rfl, le_refl _⟩
  trans h h' := ⟨h.1.trans h'.1, le_trans h.2 h'.2⟩
  add_right Z h := ⟨by simp only [Prod.fst_add, h.1], by
    simp only [Prod.snd_add, NNReal.coe_add]; linarith [h.2]⟩
  smul t h := ⟨by simp only [Prod.smul_fst, h.1], by
    simp only [Prod.smul_snd, smul_eq_mul, NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_left h.2 t.2⟩
  stability {X Y Z₀ Z₁} h := by
    have hm : ∀ n : ℕ, (X.1 : ℝ) + ((n : ℝ) + 1)⁻¹ * Z₀.1 = Y.1 + ((n : ℝ) + 1)⁻¹ * Z₁.1 := by
      intro n
      have := congrArg NNReal.toReal (h n).1
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, NNReal.coe_add,
        NNReal.coe_mul] at this
      push_cast at this
      exact this
    have h0 := hm 0
    have h1 := hm 1
    norm_num at h0 h1
    refine ⟨NNReal.coe_injective (by linarith), ?_⟩
    have h' : ∀ n : ℕ, (X.2 : ℝ) ≤ Y.2 + ((n : ℝ) + 1)⁻¹ * (Z₁.2 - Z₀.2) := by
      intro n
      have := (h n).2
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, NNReal.coe_add,
        NNReal.coe_mul] at this
      push_cast at this
      linarith
    have hlim : Tendsto (fun n : ℕ => (Y.2 : ℝ) + ((n : ℝ) + 1)⁻¹ * (Z₁.2 - Z₀.2)) atTop
        (𝓝 (Y.2 + 0 * (Z₁.2 - Z₀.2))) := by
      refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    rw [zero_mul, add_zero] at hlim
    exact ge_of_tendsto' hlim h'
  comp := LinearMap.pi fun _ => LinearMap.fst ℝ≥0 ℝ≥0 ℝ≥0
  comparison {X Y} h := by
    have hm : X.1 = Y.1 := congrFun h ()
    rcases le_total (X.2 : ℝ) Y.2 with h' | h'
    · exact Or.inl ⟨hm, h'⟩
    · exact Or.inr ⟨hm.symm, h'⟩

/-- 基準状態 `X₀ = (1, 0) ≺≺ X₁ = (1, 1)`。 -/
noncomputable def modelCalibration : Adiabatic.Calibration ModelState Unit where
  ref := LinearMap.inl ℝ≥0 ℝ≥0 ℝ≥0 ∘ₗ LinearMap.proj ()
  comp_ref k := by funext u; rfl
  X₀ := (1, 0)
  X₁ := (1, 1)
  ref_X₀ := rfl
  comp_X₁ := rfl
  strict := ⟨⟨rfl, by norm_num⟩, fun h => absurd h.2 (by norm_num)⟩

/-- モデルでは、到達性から構成したエントロピーが第二成分そのものになる。 -/
theorem model_entropy (X : ModelState) : modelCalibration.entropy X = X.2 := by
  obtain ⟨-, h⟩ := modelCalibration.entropy_unique (fun X : ModelState => (X.2 : ℝ))
    ⟨fun X Y => by simp, fun t X => by simp⟩
    (fun X Y hc => ⟨fun h => h.2, fun h => ⟨congrFun hc (), h⟩⟩)
  have := h X
  rw [show (modelCalibration.X₁.2 : ℝ) = 1 from by simp [modelCalibration],
    show (modelCalibration.X₀.2 : ℝ) = 0 from by simp [modelCalibration],
    show ((modelCalibration.base X).2 : ℝ) = 0 from rfl] at this
  linarith

/-- **近傍の Carathéodory の原理は公理から出ない**：このモデルの `X₀ = (1, 0)` からは、
組成 (質量) の等しいすべての状態に断熱的に移れる。したがって `X₀` のどの近くにも、
`X₀` から断熱的に到達できない同じ組成の状態はない。 -/
theorem model_reach_all (Y : ModelState)
    (hY : Adiabatic.comp Y = Adiabatic.comp modelCalibration.X₀) :
    Adiabatic.prec modelCalibration.X₀ Y :=
  ⟨(congrFun hY ()).symm, Y.2.2⟩

end OpThermo
