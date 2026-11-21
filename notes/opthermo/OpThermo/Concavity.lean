import OpThermo.Temperature

/-!
# エントロピーの凹性

単純系の平衡状態を座標 `x` (内部エネルギー、体積、物質量の組) で `γ x` と書く。
割合 `a : b` (`a + b = 1`) で二つの状態 `γ x`, `γ y` から部分を切り出して並べ、間の仕切りを抜くと、
座標が `a x + b y` の平衡状態に移る。この操作から次が出る。

* `Adiabatic.concaveOn_of_partition`：`x ↦ S (γ x)` は凹 (上に凸)。
* `concave_continuousOn`：一変数の凹関数は開区間上で連続。
  `merge_range` などで仮定した連続性は、凹性から出る。
* `superadditive_of_concave`：凹で一次同次な関数は優加法的 `S(x) + S(y) ≤ S(x + y)`。
* `Adiabatic.contact_reversible_of_equal_temp`：温度の等しい系の熱接触は可逆
  (接触して切り離すと元の分配に戻せる)。第零法則の「温度が等しければ何も起こらない」の向き。
-/

open Set NNReal

namespace OpThermo

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **仕切りを抜くとエントロピーは凹**：`D` の `x, y` と `a + b = 1` について、
`a • γ x + b • γ y` から仕切りを抜いて `γ (a x + b y)` に断熱的に移れ (`hpart`)、
組成が座標について線形 (`hcomp`) なら、`x ↦ S (γ x)` は `D` 上で凹。 -/
theorem concaveOn_of_partition {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : Calibration 𝒮 C) (γ : E → 𝒮) {D : Set E} (hD : Convex ℝ D)
    (hcomp : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ≥0, a + b = 1 →
      comp (γ ((a : ℝ) • x + (b : ℝ) • y)) = a • comp (γ x) + b • comp (γ y))
    (hpart : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ≥0, a + b = 1 →
      a • γ x + b • γ y ≺ γ ((a : ℝ) • x + (b : ℝ) • y)) :
    ConcaveOn ℝ D (fun x => c.entropy (γ x)) := by
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have hab' : a + b = 1 := by exact_mod_cast hab
  have hm : comp (a • γ x + b • γ y) = comp (γ ((a : ℝ) • x + (b : ℝ) • y)) := by
    rw [map_add, map_smul, map_smul, hcomp x hx y hy a b hab']
  have h := (c.entropy_principle hm).1 (hpart x hx y hy a b hab')
  rw [c.entropy_add, c.entropy_smul, c.entropy_smul] at h
  simpa only [NNReal.smul_def, smul_eq_mul] using h

end Adiabatic

/-- **凹関数は連続**：開区間 (一般に開集合) 上の凹関数は連続。 -/
theorem concave_continuousOn {s : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : ConcaveOn ℝ I s) :
    ContinuousOn s I :=
  hc.continuousOn hI

/-- **優加法性**：凸錐 `D` 上で凹かつ一次同次な関数は `f x + f y ≤ f (x + y)`。 -/
theorem superadditive_of_concave {E : Type*} [AddCommGroup E] [Module ℝ E] {D : Set E}
    {f : E → ℝ} (hc : ConcaveOn ℝ D f) (hhom : ∀ x ∈ D, f ((2 : ℝ) • x) = 2 * f x)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f x + f y ≤ f (x + y) := by
  have hmid := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hmem : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ D :=
    hc.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = x + y := by
    rw [smul_add, smul_smul, smul_smul]; norm_num
  have := hhom _ hmem
  rw [h2] at this
  simp only [smul_eq_mul] at hmid
  linarith

/-- **微分が `0` の点は凹関数の最大点**。 -/
theorem concave_max_of_deriv_zero {F : ℝ → ℝ} {K : Set ℝ} (hc : ConcaveOn ℝ K F) {x : ℝ}
    (hx : x ∈ K) (hd : HasDerivAt F 0 x) {y : ℝ} (hy : y ∈ K) : F y ≤ F x := by
  rcases lt_trichotomy x y with h | rfl | h
  · have h1 := hc.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at h1
    have := (div_le_iff₀ (sub_pos.2 h)).1 h1
    linarith
  · exact le_rfl
  · have h1 := hc.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at h1
    have := (le_div_iff₀ (sub_pos.2 h)).1 h1
    linarith

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **温度の等しい系の熱接触は可逆**：A, B のエントロピー `sA`, `sB` がそれぞれ凹で、
分配 `x` で逆温度が等しい (`sA' x = sB' (Q - x) = β`) とする。熱接触で結合系の平衡状態 `J` に移り
(`hin`)、`J` から切り離すと何らかの分配 `u` に戻れる (`hout`) なら、`J` から分配 `x` にも
断熱的に戻れる。つまり、温度の等しい二つの系を接触させ、切り離して元の分配に戻すことができ、
接触は全エントロピーを変えない。 -/
theorem contact_reversible_of_equal_temp (c : Calibration 𝒮 C) (γA γB : ℝ → 𝒮)
    {IA IB : Set ℝ} (hcA : ConcaveOn ℝ IA (fun u => c.entropy (γA u)))
    (hcB : ConcaveOn ℝ IB (fun u => c.entropy (γB u))) {Q x u β : ℝ}
    (hx : x ∈ IA) (hx' : Q - x ∈ IB) (hu : u ∈ IA) (hu' : Q - u ∈ IB)
    (hdA : HasDerivAt (fun u => c.entropy (γA u)) β x)
    (hdB : HasDerivAt (fun u => c.entropy (γB u)) β (Q - x))
    (J : 𝒮) (hJ : comp J = comp (γA x + γB (Q - x)))
    (hJu : comp J = comp (γA u + γB (Q - u)))
    (hin : γA x + γB (Q - x) ≺ J) (hout : J ≺ γA u + γB (Q - u)) :
    γA x + γB (Q - x) ∼ₐ J := by
  set K : Set ℝ := IA ∩ {y | Q - y ∈ IB}
  have hK : Convex ℝ K := by
    refine hcA.1.inter ?_
    intro y hy z hz a b ha hb hab
    have : Q - (a • y + b • z) = a • (Q - y) + b • (Q - z) := by
      simp only [smul_eq_mul]; linear_combination (-Q) * hab
    change Q - (a • y + b • z) ∈ IB
    rw [this]; exact hcB.1 hy hz ha hb hab
  have hcB' : ConcaveOn ℝ K (fun y => c.entropy (γB (Q - y))) := by
    refine ⟨hK, fun y hy z hz a b ha hb hab => ?_⟩
    have e : Q - (a • y + b • z) = a • (Q - y) + b • (Q - z) := by
      simp only [smul_eq_mul]; linear_combination (-Q) * hab
    simp only [e]
    exact hcB.2 hy.2 hz.2 ha hb hab
  have hF : ConcaveOn ℝ K (fun y => c.entropy (γA y) + c.entropy (γB (Q - y))) :=
    (hcA.subset inter_subset_left hK).add hcB'
  have hd : HasDerivAt (fun y => c.entropy (γA y) + c.entropy (γB (Q - y))) 0 x := by
    simpa using hasDerivAt_exchange hdA hdB
  have hmax := concave_max_of_deriv_zero hF ⟨hx, hx'⟩ hd (y := u) ⟨hu, hu'⟩
  have h1 := (c.entropy_principle hJu).1 hout
  rw [c.entropy_add] at h1
  refine ⟨hin, (c.entropy_principle hJ).2 ?_⟩
  rw [c.entropy_add]
  linarith

end Adiabatic

end OpThermo
