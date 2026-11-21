import OpThermo.Gibbs

/-!
# Helmholtz 自由エネルギーとエンタルピー

Gibbs 関数 `G = U + p₀ V - T₀ S` と同じ形の組み合わせを、環境の種類ごとに考える。

* Helmholtz 自由エネルギー `F = U - T₀ S`：温度 `T₀` の熱浴とだけエネルギーをやりとりする系。
  * `total_entropy_helmholtz`：理想的な熱浴では `ΔS_全体 = -ΔF / T₀`。
  * `helmholtz_criterion`：体積を変えない系では `X + R ≺ Y + R' ↔ F Y ≤ F X`。
    エントロピー原理と加法性から直接示す。
  * `CompositeOps.max_work`：熱浴と接した系から取り出せる仕事は `F` の減少分を超えない。
    「自由エネルギー」という名前の由来である。
* エンタルピー `H = U + p₀ V`：圧力 `p₀` のピストン (重りを載せた蓋) と接した系。
  * `CompositeOps.enthalpy_change`：ピストンの重り以外の仕事 (かき混ぜ、電熱) が `W'` の
    断熱操作では `ΔH = W'`。定圧の熱量測定が測るのは `ΔH` である。
  * `joule_thomson`：絞り膨張では `U₁ + p₁ V₁ = U₂ + p₂ V₂`。
* `min_of_max`、`Adiabatic.energy_minimum`、`Adiabatic.enthalpy_minimum`：エントロピー最大から
  エネルギー最小とエンタルピー最小を導く。
* `helmholtz_hasDerivAt`、`enthalpy_hasDerivAt`：`dU = T dS - p dV` の下で
  `dF = -S dT - p dV`、`dH = T dS + V dp`。
* `idealGas_enthalpy`：理想気体では `H = (c + 1) N T`。
-/

open NNReal

namespace OpThermo

/-- 温度 `T₀` の環境に対する Helmholtz 関数 `F = U - T₀ S`。 -/
def helmholtz {Γ : Type*} (S U : Γ → ℝ) (T₀ : ℝ) (X : Γ) : ℝ :=
  U X - T₀ * S X

/-- 圧力 `p₀` の環境に対するエンタルピー `H = U + p₀ V`。 -/
def enthalpy {Γ : Type*} (U V : Γ → ℝ) (p₀ : ℝ) (X : Γ) : ℝ :=
  U X + p₀ * V X

/-- Helmholtz 関数は、体積を使わない (`V = 0`, `p₀ = 0`) Gibbs 関数である。 -/
theorem helmholtz_eq_gibbs {Γ : Type*} (S U : Γ → ℝ) (T₀ : ℝ) (X : Γ) :
    helmholtz S U T₀ X = gibbs S U (fun _ => 0) T₀ 0 X := by
  simp [helmholtz, gibbs]

/-- 理想的な熱浴では、全エントロピー変化は `-ΔF / T₀` に等しい。 -/
theorem total_entropy_helmholtz {Γ : Type*} (S U : Γ → ℝ) {T₀ σ : ℝ} (hT : T₀ ≠ 0)
    {X Y : Γ} {UR UR' : ℝ} (hU : U X + UR = U Y + UR') :
    (S Y + (σ + UR' / T₀)) - (S X + (σ + UR / T₀)) =
      -(helmholtz S U T₀ Y - helmholtz S U T₀ X) / T₀ := by
  obtain rfl : UR' = U X + UR - U Y := by linarith
  unfold helmholtz
  field_simp
  ring

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **Helmholtz 自由エネルギーの最小原理** (理想的な熱浴)。系と熱浴 `R` のエネルギーの和が
保存し、熱浴のエントロピーが `σ + U / T₀` なら、`X + R ≺ Y + R' ↔ F Y ≤ F X`。 -/
theorem helmholtz_criterion (c : Calibration 𝒮 C) (U : 𝒮 → ℝ) {T₀ σ : ℝ} (hT : 0 < T₀)
    {X Y R R' : 𝒮} (hmass : comp (X + R) = comp (Y + R'))
    (hU : U X + U R = U Y + U R')
    (hR : c.entropy R = σ + U R / T₀) (hR' : c.entropy R' = σ + U R' / T₀) :
    X + R ≺ Y + R' ↔ helmholtz c.entropy U T₀ Y ≤ helmholtz c.entropy U T₀ X := by
  rw [Calibration.entropy_principle hmass, Calibration.entropy_add, Calibration.entropy_add,
    ← sub_nonneg, hR, hR', total_entropy_helmholtz c.entropy U hT.ne' hU, neg_div, neg_nonneg,
    div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hT.le⟩

end Adiabatic

/-! ### エネルギーとエンタルピーの最小原理 -/

/-- **極大から極小へ** (Callen)：集合 `P` 上で、`E` が等しい中で `S` が `x` で最大になり、
どの `y ∈ P` からも `S` を厳密に増やしながら `E` を任意に上げられるとする。
このとき、`S` が等しい中で `E` は `x` で最小になる。 -/
theorem min_of_max {α : Type*} (P : Set α) (S E : α → ℝ) {x : α}
    (hmax : ∀ y ∈ P, E y = E x → S y ≤ S x)
    (hup : ∀ y ∈ P, ∀ e, E y < e → ∃ y' ∈ P, E y' = e ∧ S y < S y') :
    ∀ y ∈ P, S y = S x → E x ≤ E y := by
  intro y hy hS
  by_contra h
  obtain ⟨y', hy', hE, hlt⟩ := hup y hy (E x) (lt_of_not_ge h)
  have := hmax y' hy' hE
  linarith

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

/-- **エネルギー最小原理**：`P` は体積と組成の等しい状態の集まりで、`X ∈ P` は内部の拘束を
外して到達する平衡状態とする。内部エネルギーの等しい `Y ∈ P` からは `X` に断熱的に移れ
(`hreach`)、かき混ぜで `S` を厳密に増やしながら `U` を上げられる (`hstir`) なら、
エントロピーの等しい状態の中で `U` は `X` で最小。 -/
theorem energy_minimum (c : Calibration 𝒮 C) (U : 𝒮 → ℝ) (P : Set 𝒮) {X : 𝒮}
    (hcomp : ∀ Y ∈ P, comp Y = comp X)
    (hreach : ∀ Y ∈ P, U Y = U X → Y ≺ X)
    (hstir : ∀ Y ∈ P, ∀ u, U Y < u → ∃ Y' ∈ P, U Y' = u ∧ c.entropy Y < c.entropy Y') :
    ∀ Y ∈ P, c.entropy Y = c.entropy X → U X ≤ U Y :=
  min_of_max P c.entropy U
    (fun Y hY hU => (c.entropy_principle (hcomp Y hY)).1 (hreach Y hY hU)) hstir

/-- **エンタルピー最小原理**：`P` は圧力 `p₀` のピストンと接した、組成の等しい状態の集まりで、
`X ∈ P` は平衡状態とする。エンタルピーの等しい `Y ∈ P` からは、ピストンの重りだけが動く
断熱操作で `X` に移れ (`hreach`)、定圧でかき混ぜれば `S` を厳密に増やしながら `H` を上げられる
(`hstir`) なら、エントロピーの等しい状態の中で `H` は `X` で最小。 -/
theorem enthalpy_minimum (c : Calibration 𝒮 C) (U V : 𝒮 → ℝ) (p₀ : ℝ) (P : Set 𝒮) {X : 𝒮}
    (hcomp : ∀ Y ∈ P, comp Y = comp X)
    (hreach : ∀ Y ∈ P, enthalpy U V p₀ Y = enthalpy U V p₀ X → Y ≺ X)
    (hstir : ∀ Y ∈ P, ∀ h, enthalpy U V p₀ Y < h →
      ∃ Y' ∈ P, enthalpy U V p₀ Y' = h ∧ c.entropy Y < c.entropy Y') :
    ∀ Y ∈ P, c.entropy Y = c.entropy X → enthalpy U V p₀ X ≤ enthalpy U V p₀ Y :=
  min_of_max P c.entropy (enthalpy U V p₀)
    (fun Y hY hH => (c.entropy_principle (hcomp Y hY)).1 (hreach Y hY hH)) hstir

end Adiabatic

namespace CompositeOps

variable {𝒮 C W : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] (O : CompositeOps 𝒮 C W)
  {m : W → ℝ} (hpi : O.PathIndependent m) (ref : (C → ℝ≥0) →ₗ[ℝ≥0] 𝒮)
  (href : ∀ k, O.comp (ref k) = k)

include hpi

/-- **最大仕事の原理**：温度 `T₀` の理想的な熱浴 `R` と接した系を `X` から `Y` に移す断熱操作で
取り出せる仕事 `-W(p)` は、Helmholtz 関数の減少分 `F(X) - F(Y)` を超えない。 -/
theorem max_work (c : O.Calibration) {T₀ σ : ℝ} (hT : 0 < T₀) {X Y R R' : 𝒮}
    (hR : O.entropy c R = σ + O.energy ref href m R / T₀)
    (hR' : O.entropy c R' = σ + O.energy ref href m R' / T₀)
    (p : O.Operation (X + R) (Y + R')) :
    -O.work m p ≤ helmholtz (O.entropy c) (O.energy ref href m) T₀ X -
      helmholtz (O.entropy c) (O.energy ref href m) T₀ Y := by
  have hE := O.energy_spec ref href hpi p
  rw [O.energy_add ref href hpi, O.energy_add ref href hpi] at hE
  have hS := (@Adiabatic.Calibration.entropy_principle 𝒮 C _ _ O.toAdiabatic c _ _
    (O.comp_eq p)).1 ⟨p⟩
  rw [@Adiabatic.Calibration.entropy_add 𝒮 C _ _ O.toAdiabatic c,
    @Adiabatic.Calibration.entropy_add 𝒮 C _ _ O.toAdiabatic c] at hS
  change O.entropy c X + O.entropy c R ≤ O.entropy c Y + O.entropy c R' at hS
  rw [hR, hR'] at hS
  have h2 : (O.energy ref href m R - O.energy ref href m R') / T₀ ≤
      O.entropy c Y - O.entropy c X := by
    rw [_root_.sub_div]; linarith
  have h3 := (div_le_iff₀ hT).1 h2
  unfold helmholtz
  linarith

/-- **エンタルピーの変化**：圧力 `p₀` のピストンと接した系の断熱操作で、仕事が
ピストンの重りの分 `-p₀ ΔV` とそれ以外 `W'` に分かれるなら、`ΔH = W'`。 -/
theorem enthalpy_change (V : 𝒮 → ℝ) {p₀ W' : ℝ} {X Y : 𝒮} (p : O.Operation X Y)
    (hW : O.work m p = W' - p₀ * (V Y - V X)) :
    enthalpy (O.energy ref href m) V p₀ Y - enthalpy (O.energy ref href m) V p₀ X = W' := by
  have hE := O.energy_spec ref href hpi p
  unfold enthalpy
  linarith

end CompositeOps

/-- **Joule–Thomson の絞り膨張**：圧力 `p₁` で押し込まれ、圧力 `p₂` で押し出される気体の
エネルギー収支 `U₂ - U₁ = p₁ V₁ - p₂ V₂` から、`U₁ + p₁ V₁ = U₂ + p₂ V₂`。 -/
theorem joule_thomson {U₁ U₂ p₁ p₂ V₁ V₂ : ℝ} (h : U₂ - U₁ = p₁ * V₁ - p₂ * V₂) :
    U₁ + p₁ * V₁ = U₂ + p₂ * V₂ := by
  linarith

/-- **`dF = -S dT - p dV`**：経路に沿って `dU = T dS - p dV` なら、`F = U - T S` の変化率は
`-S T' - p V'`。 -/
theorem helmholtz_hasDerivAt {U S T p : ℝ → ℝ} {t U' S' V' T' : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (hT : HasDerivAt T T' t)
    (hfund : U' = T t * S' - p t * V') :
    HasDerivAt (fun t => U t - T t * S t) (-S t * T' - p t * V') t := by
  convert hU.sub (hT.mul hS) using 1
  rw [hfund]; ring

/-- **`dH = T dS + V dp`**：経路に沿って `dU = T dS - p dV` なら、`H = U + p V` の変化率は
`T S' + V p'`。 -/
theorem enthalpy_hasDerivAt {U V T p : ℝ → ℝ} {t U' S' V' p' : ℝ}
    (hU : HasDerivAt U U' t) (hV : HasDerivAt V V' t) (hp : HasDerivAt p p' t)
    (hfund : U' = T t * S' - p t * V') :
    HasDerivAt (fun t => U t + p t * V t) (T t * S' + V t * p') t := by
  convert hU.add (hp.mul hV) using 1
  rw [hfund]; ring

/-- **理想気体のエンタルピー**：`U = c N T` と `p V = N T` から `H = (c + 1) N T`。 -/
theorem idealGas_enthalpy {c N T U p V : ℝ} (hU : U = c * N * T) (hpV : p * V = N * T) :
    U + p * V = (c + 1) * N * T := by
  rw [hU, hpV]; ring

end OpThermo
