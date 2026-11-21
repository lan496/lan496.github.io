import OpThermo.Entropy
import OpThermo.FirstLaw

/-!
# 複合系の断熱操作：断熱到達性と示量的な内部エネルギー

`FirstLaw.lean` の断熱操作を、状態の空間 `𝒮` (`StateSpace.lean`) の上に広げる。

## 断熱到達性

断熱到達性 `X ≺ Y` は原始概念にせず、`X` から `Y` への断熱操作が存在することと定義する
(`CompositeOps.toAdiabatic`)。Lieb–Yngvason の公理のうち、
* A1 反射律は「何もしない」断熱操作 (`idle`) から、
* A2 推移律は断熱操作を続けて行えること (`seq`) から、
* A3 は別の系を脇に置いたまま断熱操作できること (`alongside`) から、
* A4 は量を `t` 倍した系にも同じ断熱操作を行えること (`scale`) から

それぞれ従う。A6 安定性と比較仮説 CH は、断熱操作の存在についての経験的仮定として置く。

## 内部エネルギー

組成ごとの基準状態 `ref` を固定し、`ref (comp X)` と `X` を結ぶ断熱操作の仕事で `U X` を定める
(`energy`)。経路独立性の下で
* `energy_spec`：任意の断熱操作 `p : X → Y` で `U Y - U X = W(p)`、
* `energy_extensive`：`U` は示量的 (複合で足し合わされ、`t` 倍で `t` 倍になる)。
-/

open NNReal

namespace OpThermo

/-- 複合系と量を変えた系の上の断熱操作。`C` は成分の集まり。 -/
structure CompositeOps (𝒮 : Type*) [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] (C : Type*)
    (Weight : Type*) where
  /-- `Operation X Y`：`X` から `Y` へ移す断熱操作の集まり -/
  Operation : 𝒮 → 𝒮 → Type*
  /-- 二つの断熱操作を続けて行う -/
  seq : ∀ {X Y Z}, Operation X Y → Operation Y Z → Operation X Z
  /-- 断熱操作 `p` の降下の記録 -/
  drops : ∀ {X Y}, Operation X Y → WeightDrops Weight
  /-- 続けて行った断熱操作の降下の記録は、それぞれの記録をつなげたもの -/
  drops_seq : ∀ {X Y Z} (p : Operation X Y) (q : Operation Y Z),
    drops (seq p q) = drops p ++ drops q
  /-- 何もしない断熱操作 -/
  idle : ∀ X, Operation X X
  /-- 何もしなければ重りは動かない -/
  drops_idle : ∀ X, drops (idle X) = []
  /-- 別の系 `Z` を脇に置いたまま、`X` に断熱操作を行う -/
  alongside : ∀ {X Y} (Z : 𝒮), Operation X Y → Operation (X + Z) (Y + Z)
  /-- 脇に置いた系は重りの動きを変えない -/
  drops_alongside : ∀ {X Y} (Z : 𝒮) (p : Operation X Y), drops (alongside Z p) = drops p
  /-- 量を `t` 倍した系に、同じ断熱操作を行う -/
  scale : ∀ {X Y} (t : ℝ≥0), Operation X Y → Operation (t • X) (t • Y)
  /-- 量を `t` 倍すると、重りの降下量も `t` 倍になる -/
  drops_scale : ∀ {X Y} (t : ℝ≥0) (p : Operation X Y),
    drops (scale t p) = (drops p).map fun bh => (bh.1, (t : ℝ) * bh.2)
  /-- 経験的仮定 A6 (安定性)：大きさ `1/(n+1)` の補助系を使えば断熱操作で移れる、が
  全ての `n` で成り立つなら、補助系なしで移れる -/
  stability : ∀ {X Y Z₀ Z₁ : 𝒮},
    (∀ n : ℕ, Nonempty (Operation (X + ((n : ℝ≥0) + 1)⁻¹ • Z₀) (Y + ((n : ℝ≥0) + 1)⁻¹ • Z₁))) →
      Nonempty (Operation X Y)
  /-- 組成：成分ごとの質量 (天秤で測る)。複合で足し合わされ、量の変更で `t` 倍される -/
  comp : 𝒮 →ₗ[ℝ≥0] (C → ℝ≥0)
  /-- 断熱操作では物質は出入りしないので、組成は変わらない -/
  comp_eq : ∀ {X Y}, Operation X Y → comp X = comp Y
  /-- 経験的仮定 CH (比較仮説)：組成の等しい二状態は、少なくとも一方向に断熱操作で結べる -/
  comparison : ∀ {X Y}, comp X = comp Y → Nonempty (Operation X Y) ∨ Nonempty (Operation Y X)

namespace CompositeOps

variable {𝒮 : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] {C Weight : Type*}
variable (O : CompositeOps 𝒮 C Weight)

/-- **断熱到達性**：`X` から `Y` への断熱操作が存在する。この関係は A1--A6 と CH を満たす。 -/
def toAdiabatic : Adiabatic 𝒮 C where
  prec X Y := Nonempty (O.Operation X Y)
  refl X := ⟨O.idle X⟩
  trans := fun ⟨p⟩ ⟨q⟩ => ⟨O.seq p q⟩
  add_right Z := fun ⟨p⟩ => ⟨O.alongside Z p⟩
  smul t := fun ⟨p⟩ => ⟨O.scale t p⟩
  stability h := O.stability h
  comp := O.comp
  comparison h := O.comparison h

/-- 断熱操作から定めた断熱到達性に対する較正 (`Entropy.lean`) -/
abbrev Calibration := @Adiabatic.Calibration 𝒮 C _ _ O.toAdiabatic

/-- 較正 `c` によるエントロピー -/
noncomputable abbrev entropy (c : O.Calibration) : 𝒮 → ℝ :=
  @Adiabatic.Calibration.entropy 𝒮 C _ _ O.toAdiabatic c

theorem prec_iff {X Y : 𝒮} : O.toAdiabatic.prec X Y ↔ Nonempty (O.Operation X Y) := Iff.rfl

/-! ### 仕事 -/

/-- 仕事：降下の記録から計算した `Σ m(b) h` -/
def work (m : Weight → ℝ) {X Y : 𝒮} (p : O.Operation X Y) : ℝ :=
  mechanicalWork m (O.drops p)

variable (m : Weight → ℝ)

theorem work_seq {X Y Z : 𝒮} (p : O.Operation X Y) (q : O.Operation Y Z) :
    O.work m (O.seq p q) = O.work m p + O.work m q := by
  simp [work, mechanicalWork, O.drops_seq]

theorem work_idle (X : 𝒮) : O.work m (O.idle X) = 0 := by
  simp [work, mechanicalWork, O.drops_idle]

theorem work_alongside {X Y : 𝒮} (Z : 𝒮) (p : O.Operation X Y) :
    O.work m (O.alongside Z p) = O.work m p := by
  simp [work, O.drops_alongside]

theorem work_scale {X Y : 𝒮} (t : ℝ≥0) (p : O.Operation X Y) :
    O.work m (O.scale t p) = t * O.work m p := by
  simp only [work, mechanicalWork, O.drops_scale, List.map_map]
  induction O.drops p with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
    rw [ih]; ring

/-- 経路独立性 (Joule)：同じ始状態と終状態を結ぶ断熱操作の仕事は等しい。 -/
abbrev PathIndependent : Prop :=
  ∀ {X Y : 𝒮} (p q : O.Operation X Y), O.work m p = O.work m q

/-! ### 示量的な内部エネルギー -/

variable {m} (ref : (C → ℝ≥0) →ₗ[ℝ≥0] 𝒮) (href : ∀ k, O.comp (ref k) = k)

open scoped Classical in
/-- 内部エネルギー：同じ組成の基準状態 `ref (comp X)` から `X` への断熱操作の仕事。
その向きの断熱操作がなければ、逆向きの断熱操作の仕事の符号を変えたもの (CH から存在する)。 -/
noncomputable def energy (m : Weight → ℝ) (X : 𝒮) : ℝ :=
  if h : Nonempty (O.Operation (ref (O.comp X)) X) then O.work m h.some
  else -O.work m (((O.comparison (href (O.comp X))).resolve_left h).some)

variable (hpi : O.PathIndependent m)
include hpi

theorem energy_eq_of_to {R X : 𝒮} (hR : R = ref (O.comp X)) (a : O.Operation R X) :
    O.energy ref href m X = O.work m a := by
  subst hR
  have h : Nonempty (O.Operation (ref (O.comp X)) X) := ⟨a⟩
  rw [energy, dif_pos h]
  exact hpi _ _

theorem energy_eq_of_from {R X : 𝒮} (hR : R = ref (O.comp X)) (a : O.Operation X R) :
    O.energy ref href m X = -O.work m a := by
  subst hR
  unfold energy
  split_ifs with h
  · have := hpi (O.seq h.some a) (O.idle _)
    rw [work_seq, work_idle] at this
    linarith
  · rw [hpi _ a]

/-- **内部エネルギーの存在**：任意の断熱操作 `p : X → Y` で `U Y - U X = W(p)`。 -/
theorem energy_spec {X Y : 𝒮} (p : O.Operation X Y) :
    O.energy ref href m Y - O.energy ref href m X = O.work m p := by
  have hRY : ref (O.comp X) = ref (O.comp Y) := by rw [O.comp_eq p]
  rcases O.comparison (href (O.comp X)) with ha | ha
  · obtain ⟨a⟩ := ha
    rw [O.energy_eq_of_to ref href hpi rfl a, O.energy_eq_of_to ref href hpi hRY (O.seq a p),
      work_seq]
    ring
  · obtain ⟨a⟩ := ha
    rw [O.energy_eq_of_from ref href hpi rfl a]
    have hcY : O.comp (ref (O.comp X)) = O.comp Y := by rw [href, O.comp_eq p]
    rcases O.comparison hcY with hb | hb
    · obtain ⟨b⟩ := hb
      rw [O.energy_eq_of_to ref href hpi hRY b, hpi p (O.seq a b), work_seq]
      ring
    · obtain ⟨b⟩ := hb
      rw [O.energy_eq_of_from ref href hpi hRY b]
      have := hpi (O.seq p b) a
      rw [work_seq] at this
      linarith

/-- 基準状態の内部エネルギーは `0`。 -/
theorem energy_ref (k : C → ℝ≥0) : O.energy ref href m (ref k) = 0 := by
  rw [O.energy_eq_of_to ref href hpi (by rw [href]) (O.idle (ref k)), work_idle]

/-- 組成の等しい状態の差は、脇に別の系を置いても変わらない。 -/
theorem energy_add_sub {X Y : 𝒮} (h : O.comp X = O.comp Y) (Z : 𝒮) :
    O.energy ref href m (X + Z) - O.energy ref href m (Y + Z) =
      O.energy ref href m X - O.energy ref href m Y := by
  rcases O.comparison h with hp | hp
  · obtain ⟨p⟩ := hp
    have h1 := O.energy_spec ref href hpi p
    have h2 := O.energy_spec ref href hpi (O.alongside Z p)
    rw [work_alongside] at h2
    linarith
  · obtain ⟨p⟩ := hp
    have h1 := O.energy_spec ref href hpi p
    have h2 := O.energy_spec ref href hpi (O.alongside Z p)
    rw [work_alongside] at h2
    linarith

/-- **加法性**：`U (X + Y) = U X + U Y`。 -/
theorem energy_add (X Y : 𝒮) :
    O.energy ref href m (X + Y) = O.energy ref href m X + O.energy ref href m Y := by
  have h1 := O.energy_add_sub ref href hpi (X := X) (Y := ref (O.comp X)) (href _).symm Y
  have h2 := O.energy_add_sub ref href hpi (X := Y) (Y := ref (O.comp Y)) (href _).symm
    (ref (O.comp X))
  rw [add_comm Y, add_comm (ref (O.comp Y))] at h2
  have h3 : ref (O.comp X) + ref (O.comp Y) = ref (O.comp (X + Y)) := by simp
  rw [h3, O.energy_ref ref href hpi, O.energy_ref ref href hpi] at h2
  rw [O.energy_ref ref href hpi] at h1
  linarith

/-- **示量性**：`U (t • X) = t * U X`。 -/
theorem energy_smul (t : ℝ≥0) (X : 𝒮) :
    O.energy ref href m (t • X) = t * O.energy ref href m X := by
  have hR : t • ref (O.comp X) = ref (O.comp (t • X)) := by simp
  have h0 := O.energy_ref ref href hpi (O.comp X)
  have ht0 := O.energy_ref ref href hpi (O.comp (t • X))
  rcases O.comparison (href (O.comp X)) with hp | hp
  · obtain ⟨p⟩ := hp
    have h1 := O.energy_spec ref href hpi p
    have h2 := O.energy_spec ref href hpi (O.scale t p)
    rw [work_scale, hR] at h2
    rw [ht0] at h2
    rw [h0] at h1
    rw [← h1] at h2
    linarith
  · obtain ⟨p⟩ := hp
    have h1 := O.energy_spec ref href hpi p
    have h2 := O.energy_spec ref href hpi (O.scale t p)
    rw [work_scale, hR] at h2
    rw [ht0] at h2
    rw [h0] at h1
    linarith [show (t : ℝ) * O.work m p = -(t * O.energy ref href m X) by rw [← h1]; ring]

/-- 内部エネルギーは示量的な関数である。 -/
theorem energy_extensive : IsExtensive (O.energy ref href m) :=
  ⟨O.energy_add ref href hpi, O.energy_smul ref href hpi⟩

end CompositeOps

end OpThermo
