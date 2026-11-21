import OpThermo.Entropy

/-!
# 温度・圧力・化学ポテンシャル：保存量の交換平衡

二つの系 A, B が保存量 `q` (エネルギー、体積、成分 `i` の量 `N_i` のいずれか) を交換でき、
合計 `Q` は一定とする。A の取り分を `x` とすると全エントロピーは
`f x + g (Q - x)` である (`f`, `g` は各系のエントロピーを `q` の関数として見たもの)。

## 仮定

* `f`, `g` が微分可能であること (`HasDerivAt`)。
* 接触後の平衡では、取り分 `x` が全エントロピーを (局所的に) 最大にすること
  (`IsLocalMax`)。エントロピー原理からは「到達可能な変化で全エントロピーは減らない」
  ことまでしか出ない。平衡が最大点になるには、取り分を変える断熱操作がどちら向きにも
  断熱操作として実行できることを仮定する必要がある。

## 主結果

* `exchange_equilibrium`：平衡では `∂S_A/∂q = ∂S_B/∂q`。
  `q = U` なら `1/T_A = 1/T_B`、`q = V` なら `p_A/T_A = p_B/T_B`、
  `q = N_i` なら成分ごとに `μ_{A,i}/T_A = μ_{B,i}/T_B`。
* `exchange_direction`：`∂S_A/∂q > ∂S_B/∂q` なら、`q` を A に移す向きで全エントロピーが
  増える。`q = U` では、温度の低い系 (`1/T` が大きい系) にエネルギーが流れる。
* `fundamental_relation`、`clausius`：`dS = (1/T) dU + (p/T) dV` から
  `dU = T dS - p dV` と `dS = δQ_rev / T` を得る。
* `fundamental_relation_multi`：多成分系では `dU = T dS - p dV + Σ μ_i dN_i`
  (`μ_i := -T ∂S/∂N_i`)。
* `euler_homogeneous`：示量的な (一次同次な) 微分可能関数は `S x = S'(x) x` を満たす。
* `gibbs_euler`：これを `S(U, V, N)` に使うと `U + p V - T S = Σ μ_i N_i`。

## 温度の定義

単純系では、平衡状態は内部エネルギー、体積、組成で決まる (経験則)。
体積と組成を固定すると、実現できる内部エネルギーは区間 `I` をなし、`u ∈ I` の状態 `γ u` が一つに決まる。
エントロピーをエネルギーの関数 `s u := S (γ u)` として見たとき、
逆温度を `β := s'(u)`、温度を `T := 1/β` と定義する (`invTemp`, `temperature`)。

* `entropy_monotone_of_stirring`：かき混ぜで `γ u ≺ γ v` (`u ≤ v`) なら `s` は `I` 上で単調。
* `invTemp_nonneg`、`temperature_pos`：したがって `I` の内点で `β ≥ 0` であり、`β ≠ 0` なら `T > 0`。
* `contact_maximizes`、`contact_isLocalMax`：結合系の平衡状態がエネルギーの合計で決まるなら、
  熱接触の平衡の分配は全エントロピーを最大にする (エントロピー原理から導く)。
* `exchange_temperature`：熱接触の平衡では温度が等しい。
* `zeroth_law`：温度が等しいことは推移的 (熱力学第零法則)。
* `heat_flows_to_colder`：エネルギーを温度の低い系に移す向きで全エントロピーが増える。
* `ideal_gas`：`s u = a log u + b` なら `T = u / a`。`ideal_gas_law`：さらに `∂S/∂V = N / V` なら `p V = N T`。
* `entropy_calorimetry`：`S(v) - S(u) = ∫ β du = ∫ du / T`。かき混ぜの仕事と温度計の読みからエントロピー差を測る。
-/

open Filter Topology Set NNReal

namespace OpThermo

/-- 全エントロピー `x ↦ f x + g (Q - x)` の微分。 -/
theorem hasDerivAt_exchange {f g : ℝ → ℝ} {Q u f' g' : ℝ}
    (hf : HasDerivAt f f' u) (hg : HasDerivAt g g' (Q - u)) :
    HasDerivAt (fun x => f x + g (Q - x)) (f' - g') u := by
  have hg' : HasDerivAt (fun x => g (Q - x)) (-g') u := hg.comp_const_sub Q u
  convert hf.add hg' using 1

/-- **交換平衡**：全エントロピーが極大となる分配では、両系の `∂S/∂q` が等しい。 -/
theorem exchange_equilibrium {f g : ℝ → ℝ} {Q u f' g' : ℝ}
    (hf : HasDerivAt f f' u) (hg : HasDerivAt g g' (Q - u))
    (hmax : IsLocalMax (fun x => f x + g (Q - x)) u) : f' = g' := by
  have := hmax.hasDerivAt_eq_zero (hasDerivAt_exchange hf hg)
  linarith

/-- **交換の向き**：`∂S_A/∂q > ∂S_B/∂q` なら、A に `q` を少し移すと全エントロピーが増える。 -/
theorem exchange_direction {f g : ℝ → ℝ} {Q u f' g' : ℝ}
    (hf : HasDerivAt f f' u) (hg : HasDerivAt g g' (Q - u)) (h : g' < f') :
    ∀ᶠ x in 𝓝[>] u, f u + g (Q - u) < f x + g (Q - x) := by
  set F := fun x => f x + g (Q - x)
  have hF := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_exchange hf hg)
  have hF' : Tendsto (slope F u) (𝓝[>] u) (𝓝 (f' - g')) :=
    hF.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt (mem_Ioi.1 hx)))
  filter_upwards [hF'.eventually (lt_mem_nhds (sub_pos.2 h)), self_mem_nhdsWithin] with x hx hux
  rw [slope_def_field] at hx
  have := (div_pos_iff_of_pos_right (sub_pos.2 (mem_Ioi.1 hux))).1 hx
  simp only [F] at this
  linarith

/-- **基本関係式**：経路に沿って `dS = β dU + π dV` (`β = ∂S/∂U`, `π = ∂S/∂V`) のとき、
`T := 1/β`, `p := π/β` と定義すれば `dU = T dS - p dV`。 -/
theorem fundamental_relation {dU dV dS β π : ℝ} (hβ : β ≠ 0) (h : dS = β * dU + π * dV) :
    dU = β⁻¹ * dS - (π / β) * dV := by
  rw [h]; field_simp; ring

/-- **基本関係式を全微分の等式として**：座標 `(U, V)` の上で、`dU`, `dV` を座標関数の微分
(`fst`, `snd`)、`dS` を `S` の微分 (線形写像) とする。`dS = β dU + π dV` なら、線形写像として
`dU = β⁻¹ dS - (π/β) dV`。`fundamental_relation` はこれを一つの変位に代入した形である。 -/
theorem fundamental_relation_forms {β π : ℝ} (hβ : β ≠ 0) {S : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : fderiv ℝ S x = β • ContinuousLinearMap.fst ℝ ℝ ℝ + π • ContinuousLinearMap.snd ℝ ℝ ℝ) :
    ContinuousLinearMap.fst ℝ ℝ ℝ =
      β⁻¹ • fderiv ℝ S x - (π / β) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  ext
  · simp [h]; field_simp
  · simp [h]; field_simp; ring

/-- **Clausius の関係**：準静的過程で仕事が `-p dV` なら、熱は `δQ = dU + p dV` であり、
`dS = δQ / T`。熱をエントロピーの定義に使わず、結果として得る。 -/
theorem clausius {dU dV dS T p : ℝ} (hT : T ≠ 0) (h : dU = T * dS - p * dV) :
    dS = (dU + p * dV) / T := by
  rw [h]; field_simp; ring

/-- **多成分系の基本関係式**：`dS = β dU + π dV + Σ κ_i dN_i` (`κ_i = ∂S/∂N_i`) のとき、
`T := 1/β`, `p := π/β`, `μ_i := -κ_i/β` とおけば `dU = T dS - p dV + Σ μ_i dN_i`。 -/
theorem fundamental_relation_multi {ι : Type*} (s : Finset ι) {dU dV dS β π : ℝ}
    (κ dN : ι → ℝ) (hβ : β ≠ 0)
    (h : dS = β * dU + π * dV + ∑ i ∈ s, κ i * dN i) :
    dU = β⁻¹ * dS - (π / β) * dV + ∑ i ∈ s, (-κ i / β) * dN i := by
  have hsum : ∑ i ∈ s, (-κ i / β) * dN i = -β⁻¹ * ∑ i ∈ s, κ i * dN i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
  rw [hsum, h]; field_simp; ring

/-- **Euler の関係**：`S (t • x) = t * S x` (`t > 0`) を満たす関数が `x` で微分可能なら、
`S' x = S x`。示量的な関数の微分を、その点での値と結びつける。 -/
theorem euler_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E → ℝ} {S' : E →L[ℝ] ℝ} {x : E} (hS : HasFDerivAt S S' x)
    (hom : ∀ t : ℝ, 0 < t → S (t • x) = t * S x) : S' x = S x := by
  have h1 : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h2 : HasDerivAt (fun t : ℝ => S (t • x)) (S' x) 1 := by
    have hS1 : HasFDerivAt S S' ((1 : ℝ) • x) := by simpa using hS
    exact hS1.comp_hasDerivAt (1 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => t * S x) (S x) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (S x)
  have heq : (fun t : ℝ => S (t • x)) =ᶠ[𝓝 1] fun t => t * S x := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 from one_pos)] with t ht
    exact hom t ht
  exact h2.unique (h3.congr_of_eventuallyEq heq)

/-- **Gibbs 関数と化学ポテンシャル**：Euler の関係 `S = β U + π V + Σ κ_i N_i` のもとで、
`T := 1/β`, `p := π/β`, `μ_i := -κ_i/β` とおくと `U + p V - T S = Σ μ_i N_i`。 -/
theorem gibbs_euler {ι : Type*} (s : Finset ι) {U V S β π : ℝ} (κ N : ι → ℝ) (hβ : β ≠ 0)
    (h : S = β * U + π * V + ∑ i ∈ s, κ i * N i) :
    U + (π / β) * V - β⁻¹ * S = ∑ i ∈ s, (-κ i / β) * N i := by
  have hsum : ∑ i ∈ s, (-κ i / β) * N i = -β⁻¹ * ∑ i ∈ s, κ i * N i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
  rw [hsum, h]; field_simp; ring

/-! ### 温度の定義 -/

/-- **逆温度**：エネルギーの関数としてのエントロピー `s` の微分 `β = ds/du`。 -/
noncomputable def invTemp (s : ℝ → ℝ) (u : ℝ) : ℝ := deriv s u

/-- **温度**：`T := 1/β`。 -/
noncomputable def temperature (s : ℝ → ℝ) (u : ℝ) : ℝ := (invTemp s u)⁻¹

/-- **温度の単位**：エントロピーを `a * s + b` に取り替えると、温度は `1/a` 倍になる。
エントロピーの単位を選ぶことと、温度の単位を選ぶことは同じである。 -/
theorem temperature_rescale {s : ℝ → ℝ} {u : ℝ} (a b : ℝ) (hs : DifferentiableAt ℝ s u) :
    temperature (fun x => a * s x + b) u = temperature s u / a := by
  unfold temperature invTemp
  rw [deriv_add_const, deriv_const_mul _ hs, mul_inv]
  ring

/-- **Kelvin の温度比**：温度 `T₁`, `T₂` の理想的な熱浴のエントロピー変化は `Q₁ / T₁`, `Q₂ / T₂`。
全エントロピーを保つ (可逆な) 操作で熱浴が受け取るエネルギー `Q₁`, `Q₂` の比は、
温度の比で決まる：`T₁ / T₂ = -(Q₁ / Q₂)`。 -/
theorem kelvin_ratio {T₁ T₂ Q₁ Q₂ : ℝ} (h₁ : T₁ ≠ 0) (h₂ : T₂ ≠ 0) (hQ : Q₂ ≠ 0)
    (hS : Q₁ / T₁ + Q₂ / T₂ = 0) : T₁ / T₂ = -(Q₁ / Q₂) := by
  field_simp at hS ⊢
  linarith

section Stirring

open Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **かき混ぜで上がるエントロピー**：エネルギーの区間 `I` 上の状態の族 `γ` (体積と組成を固定し、
内部エネルギー `u` の状態が `γ u`) について、組成が変わらず、かき混ぜで `u ≤ v` なら `γ u ≺ γ v`
とする。このときエネルギーの関数としてのエントロピー `u ↦ S (γ u)` は `I` 上で単調非減少。 -/
theorem entropy_monotone_of_stirring (c : Calibration 𝒮 C) (γ : ℝ → 𝒮) (I : Set ℝ)
    (hcomp : ∀ u ∈ I, ∀ v ∈ I, comp (γ u) = comp (γ v))
    (hstir : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → γ u ≺ γ v) :
    MonotoneOn (fun u => c.entropy (γ u)) I :=
  fun u hu v hv huv => (c.entropy_principle (hcomp u hu v hv)).1 (hstir u hu v hv huv)

/-- かき混ぜがあれば、区間の内点で逆温度は非負。 -/
theorem invTemp_nonneg (c : Calibration 𝒮 C) (γ : ℝ → 𝒮) (I : Set ℝ)
    (hcomp : ∀ u ∈ I, ∀ v ∈ I, comp (γ u) = comp (γ v))
    (hstir : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → γ u ≺ γ v) {u : ℝ} (hu : I ∈ 𝓝 u) :
    0 ≤ invTemp (fun u => c.entropy (γ u)) u := by
  rw [invTemp, ← derivWithin_of_mem_nhds hu]
  exact (entropy_monotone_of_stirring c γ I hcomp hstir).derivWithin_nonneg

/-- かき混ぜがあり、逆温度が `0` でなければ温度は正。 -/
theorem temperature_pos (c : Calibration 𝒮 C) (γ : ℝ → 𝒮) (I : Set ℝ)
    (hcomp : ∀ u ∈ I, ∀ v ∈ I, comp (γ u) = comp (γ v))
    (hstir : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → γ u ≺ γ v) {u : ℝ} (hu : I ∈ 𝓝 u)
    (hβ : invTemp (fun u => c.entropy (γ u)) u ≠ 0) :
    0 < temperature (fun u => c.entropy (γ u)) u :=
  inv_pos.2 (lt_of_le_of_ne (invTemp_nonneg c γ I hcomp hstir hu) (Ne.symm hβ))

/-- **熱接触の平衡はエントロピーの和を最大にする**：A, B のエネルギーで並べた状態の族を
`γA`, `γB` (区間 `IA`, `IB`) とする。エネルギーの合計が `Q` の結合系の平衡状態を `J` とし、
どの分配 `x` から接触させても `J` に移れ (`hin`)、`J` を切り離すと分配 `u` になる (`hout`) とする。
`J` が分配 `x` によらないことが、結合系の平衡状態が合計で決まるという経験則の内容である。
このとき分配 `u` は `S_A + S_B` を最大にする。 -/
theorem contact_maximizes (c : Calibration 𝒮 C) (γA γB : ℝ → 𝒮) (IA IB : Set ℝ)
    (hA : ∀ u ∈ IA, ∀ v ∈ IA, comp (γA u) = comp (γA v))
    (hB : ∀ u ∈ IB, ∀ v ∈ IB, comp (γB u) = comp (γB v))
    {Q u : ℝ} (hu : u ∈ IA) (hu' : Q - u ∈ IB) (J : 𝒮)
    (hin : ∀ x ∈ IA, Q - x ∈ IB → γA x + γB (Q - x) ≺ J)
    (hout : J ≺ γA u + γB (Q - u)) {x : ℝ} (hx : x ∈ IA) (hx' : Q - x ∈ IB) :
    c.entropy (γA x) + c.entropy (γB (Q - x)) ≤ c.entropy (γA u) + c.entropy (γB (Q - u)) := by
  have hc : comp (γA x + γB (Q - x)) = comp (γA u + γB (Q - u)) := by
    rw [map_add, map_add, hA x hx u hu, hB _ hx' _ hu']
  have := (c.entropy_principle hc).1 (trans (hin x hx hx') hout)
  rwa [c.entropy_add, c.entropy_add] at this

/-- 分配 `u` が両方の区間の内点なら、`u` は全エントロピーの極大点。 -/
theorem contact_isLocalMax (c : Calibration 𝒮 C) (γA γB : ℝ → 𝒮) (IA IB : Set ℝ)
    (hA : ∀ u ∈ IA, ∀ v ∈ IA, comp (γA u) = comp (γA v))
    (hB : ∀ u ∈ IB, ∀ v ∈ IB, comp (γB u) = comp (γB v))
    {Q u : ℝ} (hu : IA ∈ 𝓝 u) (hu' : IB ∈ 𝓝 (Q - u)) (J : 𝒮)
    (hin : ∀ x ∈ IA, Q - x ∈ IB → γA x + γB (Q - x) ≺ J)
    (hout : J ≺ γA u + γB (Q - u)) :
    IsLocalMax (fun x => c.entropy (γA x) + c.entropy (γB (Q - x))) u := by
  have hsub : ∀ᶠ x in 𝓝 u, Q - x ∈ IB :=
    ((continuous_const.sub continuous_id).continuousAt (x := u)).preimage_mem_nhds hu'
  filter_upwards [hu, hsub] with x hx hx'
  exact contact_maximizes c γA γB IA IB hA hB (mem_of_mem_nhds hu) (mem_of_mem_nhds hu') J
    hin hout hx hx'

end Stirring

/-- **熱接触の平衡では温度が等しい**：エネルギーを交換する二つの系の全エントロピーが
分配 `u` で極大なら、`T_A(u) = T_B(Q - u)`。 -/
theorem exchange_temperature {f g : ℝ → ℝ} {Q u βA βB : ℝ}
    (hf : HasDerivAt f βA u) (hg : HasDerivAt g βB (Q - u))
    (hmax : IsLocalMax (fun x => f x + g (Q - x)) u) :
    temperature f u = temperature g (Q - u) := by
  simp only [temperature, invTemp, hf.deriv, hg.deriv, exchange_equilibrium hf hg hmax]

/-- **熱力学第零法則**：A と B、B と C がそれぞれ熱平衡 (温度が等しい) なら、A と C も
温度が等しい。温度を数で定めたので、推移律は等号の推移律になる。 -/
theorem zeroth_law {TA TB TC : ℝ} (hAB : TA = TB) (hBC : TB = TC) : TA = TC :=
  hAB.trans hBC

/-- **熱は温度の高い系から低い系へ流れる**：温度が正で `T_A(u) < T_B(Q - u)` なら、
A にエネルギーを少し移すと全エントロピーが増える。 -/
theorem heat_flows_to_colder {f g : ℝ → ℝ} {Q u βA βB : ℝ}
    (hf : HasDerivAt f βA u) (hg : HasDerivAt g βB (Q - u)) (hA : 0 < βA) (hB : 0 < βB)
    (hT : temperature f u < temperature g (Q - u)) :
    ∀ᶠ x in 𝓝[>] u, f u + g (Q - u) < f x + g (Q - x) := by
  simp only [temperature, invTemp, hf.deriv, hg.deriv] at hT
  exact exchange_direction hf hg ((inv_lt_inv₀ hA hB).1 hT)

/-- **例：理想気体**：エネルギーの関数としてのエントロピーが `a log u + b` (`a > 0`) なら
温度は `T = u / a`、つまり `u = a T`。 -/
theorem ideal_gas {a b u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    temperature (fun u => a * Real.log u + b) u = u / a := by
  have h : HasDerivAt (fun u => a * Real.log u + b) (a * u⁻¹) u :=
    ((Real.hasDerivAt_log hu.ne').const_mul a).add_const b
  simp only [temperature, invTemp, h.deriv]
  field_simp

/-- **例：理想気体の状態方程式**：`β = a / u`、`π = ∂S/∂V = N / V` なら、`p := π / β` と
`T = u / a` は `p V = N T` を満たす。 -/
theorem ideal_gas_law {a u N V : ℝ} (ha : 0 < a) (hu : 0 < u) (hV : 0 < V) :
    (N / V) / (a / u) * V = N * (u / a) := by
  field_simp

/-- **熱量測定によるエントロピー差**：体積と組成を固定してかき混ぜ、エネルギーを `u` から `v` に
上げるとき、`S(v) - S(u) = ∫ β(x) dx = ∫ dx / T(x)`。
エネルギーの増分はかき混ぜの仕事 (重りの降下) で、`T` は温度計で測る。 -/
theorem entropy_calorimetry {s : ℝ → ℝ} {u v : ℝ}
    (hs : ∀ x ∈ Set.uIcc u v, DifferentiableAt ℝ s x)
    (hint : IntervalIntegrable (invTemp s) MeasureTheory.volume u v) :
    s v - s u = ∫ x in u..v, invTemp s x :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => (hs x hx).hasDerivAt) hint).symm

/-! ### 理想気体 -/

/-- **理想気体のエントロピー**：`S(U, V, N) = N (c log (U/N) + log (V/N) + s₀)`。
`c` は単原子気体で `3/2` (エントロピーの単位を Boltzmann 定数にとる)。 -/
noncomputable def idealGasEntropy (c s₀ U V N : ℝ) : ℝ :=
  N * (c * Real.log (U / N) + Real.log (V / N) + s₀)

variable {c s₀ U V N : ℝ}

/-- `∂S/∂U = c N / U`。 -/
theorem idealGas_hasDerivAt_U (hU : 0 < U) (hN : 0 < N) :
    HasDerivAt (fun U => idealGasEntropy c s₀ U V N) (c * N / U) U := by
  have h1 : HasDerivAt (fun U => U / N) (1 / N) U := by
    simpa using (hasDerivAt_id U).div_const N
  have h2 := h1.log (div_pos hU hN).ne'
  have h3 := ((h2.const_mul c).add_const (Real.log (V / N) + s₀)).const_mul N
  convert h3 using 1
  · funext U; simp only [idealGasEntropy]; ring
  · field_simp

/-- `∂S/∂V = N / V`。 -/
theorem idealGas_hasDerivAt_V (hV : 0 < V) (hN : 0 < N) :
    HasDerivAt (fun V => idealGasEntropy c s₀ U V N) (N / V) V := by
  have h1 : HasDerivAt (fun V => V / N) (1 / N) V := by
    simpa using (hasDerivAt_id V).div_const N
  have h2 := h1.log (div_pos hV hN).ne'
  have h3 := (h2.const_add (c * Real.log (U / N))).add_const s₀ |>.const_mul N
  convert h3 using 1
  · funext V; simp only [idealGasEntropy]
  · field_simp

/-- **理想気体の温度**：`T = U / (c N)`、つまり `U = c N T`。 -/
theorem idealGas_temperature (hc : 0 < c) (hU : 0 < U) (hN : 0 < N) :
    temperature (fun U => idealGasEntropy c s₀ U V N) U = U / (c * N) := by
  simp only [temperature, invTemp, (idealGas_hasDerivAt_U (c := c) (s₀ := s₀) (V := V) hU hN).deriv]
  field_simp

/-- **理想気体の状態方程式**：`p := (∂S/∂V) / (∂S/∂U)` は `p V = N T` を満たす。 -/
theorem idealGas_law (hc : 0 < c) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) :
    (N / V) / (c * N / U) * V = N * (U / (c * N)) := by
  field_simp

/-- **理想気体のエントロピーは示量的**：`S(tU, tV, tN) = t S(U, V, N)`。 -/
theorem idealGas_homogeneous {t : ℝ} (ht : 0 < t) (hN : 0 < N) :
    idealGasEntropy c s₀ (t * U) (t * V) (t * N) = t * idealGasEntropy c s₀ U V N := by
  have e1 : t * U / (t * N) = U / N := by field_simp
  have e2 : t * V / (t * N) = V / N := by field_simp
  simp only [idealGasEntropy, e1, e2]; ring

/-- 正の実数上で微分が `0` の関数は定数。 -/
theorem const_of_hasDerivAt_zero_pos {f : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f 0 x)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : f x = f y :=
  (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun z hz => (hf z (mem_Ioi.1 hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z (mem_Ioi.1 hz)).deriv) (mem_Ioi.2 hx) (mem_Ioi.2 hy)

/-- **理想気体の特徴づけ**：関数 `S(U, V, N)` が示量的で、`∂S/∂U = c N / U` と
`∂S/∂V = N / V` を満たすなら、`S` は理想気体のエントロピーで、定数は `s₀ = S(1, 1, 1)`。
温度を使わない主張である。温度と圧力の定義で読みかえると、条件は `U = c N T` と `p V = N T`。 -/
theorem idealGas_unique (S : ℝ → ℝ → ℝ → ℝ) {c : ℝ}
    (hU : ∀ U V N, 0 < U → 0 < V → 0 < N → HasDerivAt (fun U => S U V N) (c * N / U) U)
    (hV : ∀ U V N, 0 < U → 0 < V → 0 < N → HasDerivAt (fun V => S U V N) (N / V) V)
    (hom : ∀ t U V N, 0 < t → 0 < U → 0 < V → 0 < N → S (t * U) (t * V) (t * N) = t * S U V N)
    {U V N : ℝ} (hU0 : 0 < U) (hV0 : 0 < V) (hN0 : 0 < N) :
    S U V N = idealGasEntropy c (S 1 1 1) U V N := by
  -- `S - N (c log U + log V)` は `U` にも `V` にもよらない
  have stepU : ∀ U V N, 0 < U → 0 < V → 0 < N →
      S U V N - N * (c * Real.log U + Real.log V) =
        S 1 V N - N * (c * Real.log 1 + Real.log V) := by
    intro U V N hU0 hV0 hN0
    refine const_of_hasDerivAt_zero_pos (f := fun U => S U V N - N * (c * Real.log U + Real.log V))
      (fun x hx => ?_) hU0 one_pos
    have h := (hU x V N hx hV0 hN0).sub
      ((((Real.hasDerivAt_log hx.ne').const_mul c).add_const (Real.log V)).const_mul N)
    convert h using 1
    field_simp; ring
  have stepV : ∀ V N, 0 < V → 0 < N →
      S 1 V N - N * Real.log V = S 1 1 N - N * Real.log 1 := by
    intro V N hV0 hN0
    refine const_of_hasDerivAt_zero_pos (f := fun V => S 1 V N - N * Real.log V)
      (fun x hx => ?_) hV0 one_pos
    have h := (hV 1 x N one_pos hx hN0).sub ((Real.hasDerivAt_log hx.ne').const_mul N)
    convert h using 1
    field_simp; ring
  have hS : ∀ U V N, 0 < U → 0 < V → 0 < N →
      S U V N = N * (c * Real.log U + Real.log V) + S 1 1 N := by
    intro U V N hU0 hV0 hN0
    have h1 := stepU U V N hU0 hV0 hN0
    have h2 := stepV V N hV0 hN0
    simp only [Real.log_one, mul_zero, zero_add, sub_zero] at h1 h2
    linarith
  -- 示量性から `S(1, 1, N)` が決まる
  have hN : S 1 1 N = N * S 1 1 1 - N * (c + 1) * Real.log N := by
    have h := hom N 1 1 1 hN0 one_pos one_pos one_pos
    simp only [mul_one] at h
    rw [hS N N N hN0 hN0 hN0] at h
    linear_combination h
  rw [hS U V N hU0 hV0 hN0, hN, idealGasEntropy, Real.log_div hU0.ne' hN0.ne',
    Real.log_div hV0.ne' hN0.ne']
  ring

/-! ### 第三法則と到達不能性 -/

/-- **絶対零度の到達不能性**：制御変数 (体積など) の値 `i` ごとに、温度の関数としての
エントロピー `s i` が正の温度 `(0, ∞)` 上で狭義単調増加とする。Nernst の熱定理として、
`T → +0` の極限が `i` によらない共通の値 `L` であるとし (`hlim`)、零度での値をその極限で
定める (`hend`)。系に次の二種類の操作を繰り返す。

* 等温操作：温度を保ったまま制御変数を変える (溜めと熱をやりとりしてよい)。
* 断熱操作：エントロピーは減らない (エントロピー原理)。

このとき、正の温度から始めると、何回操作しても温度は正のままである。 -/
theorem unattainability {ι : Type*} (s : ι → ℝ → ℝ) (hmono : ∀ i, StrictMonoOn (s i) (Ioi 0))
    (L : ℝ) (hlim : ∀ i, Tendsto (s i) (𝓝[>] 0) (𝓝 L)) (hend : ∀ i, s i 0 = L)
    (idx : ℕ → ι) (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (hstep : ∀ n, T (n + 1) = T n ∨ s (idx n) (T n) ≤ s (idx (n + 1)) (T (n + 1)))
    (h0 : 0 < T 0) (n : ℕ) : 0 < T n := by
  have key : ∀ i (t : ℝ), 0 < t → L < s i t := by
    intro i t ht
    have h2 : (0 : ℝ) < t / 2 := by positivity
    have hle : L ≤ s i (t / 2) := by
      apply le_of_tendsto (hlim i)
      filter_upwards [Ioo_mem_nhdsGT h2] with y hy
      exact (hmono i hy.1 h2 hy.2).le
    exact hle.trans_lt (hmono i h2 ht (half_lt_self ht))
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hstep n with h | h
    · rw [h]; exact ih
    · rcases (hT (n + 1)).lt_or_eq with hpos | hzero
      · exact hpos
      · exfalso
        rw [← hzero, hend] at h
        have := key (idx n) (T n) ih
        linarith

end OpThermo
