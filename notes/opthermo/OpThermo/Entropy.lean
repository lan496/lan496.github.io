import OpThermo.StateSpace

/-!
# 断熱到達性からエントロピーを構成する (Lieb–Yngvason)

## 設定

状態の全体 `𝒮` は、複合 (`+`) とスケーリング (`t • X`, `t : ℝ≥0`) を持つ
`ℝ≥0` 加群とする (`StateSpace.lean`)。`0` は「何もない系」を表す。
系は成分 (物質の種類) の集まり `C` からなり、組成 `comp X : C → ℝ≥0` は成分ごとの質量である。

加群の公理を等式として課すことは、Lieb–Yngvason の A5 (分割・再結合) を `∼` ではなく `=`
で置いたものにあたる。

## 公理 (`Adiabatic` クラス)

* A1 `refl`、A2 `trans`：`≺` は前順序
* A3 `add_right`：別の系を添えても到達できる
* A4 `smul`：系の量を変えても到達できる
* A5：加群構造に組み込み済み (`split_recombine` として定理の形で示す)
* A6 `stability`：無限小の補助系で到達性は変わらない
* CH `comparison`：組成が等しい二状態は、少なくとも一方向に到達できる

## 主結果

基準状態 `X₀ ≺≺ X₁` (組成は等しい) と、組成ごとの基準状態 `ref` (`Calibration`) を固定すると、
* `entropy_principle`：組成が等しければ `X ≺ Y ↔ S X ≤ S Y`
* `entropy_extensive`：`S` は示量的
* `entropy_X₀`、`entropy_X₁`：`S X₀ = 0`、`S X₁ = 1`
* `entropy_unique`：以上の性質を持つ関数は `a * S + S' ∘ ref ∘ comp` (`a > 0`) に限る

途中で、A6 から相殺則 `cancel` (Lieb–Yngvason の Theorem 2.1) を導く。
-/

open NNReal Set Filter Topology

namespace OpThermo

/-- 断熱到達性の公理系。`prec X Y` は「平衡状態 `X` から `Y` へ断熱操作で到達できる」。 -/
class Adiabatic (𝒮 : Type*) (C : outParam Type*) [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] where
  /-- 断熱到達性 `X ≺ Y` -/
  prec : 𝒮 → 𝒮 → Prop
  /-- A1 反射律：何もしなければ同じ状態にとどまる -/
  refl : ∀ X, prec X X
  /-- A2 推移律：操作を続けて実行できる -/
  trans : ∀ {X Y Z}, prec X Y → prec Y Z → prec X Z
  /-- A3 結合との整合性：別の系 `Z` を添えたまま操作できる -/
  add_right : ∀ {X Y} (Z : 𝒮), prec X Y → prec (X + Z) (Y + Z)
  /-- A4 スケーリング：系の量を `t` 倍しても操作できる -/
  smul : ∀ {X Y} (t : ℝ≥0), prec X Y → prec (t • X) (t • Y)
  /-- A6 安定性：大きさ `1/(n+1)` の補助系を使えば到達できる、が全ての `n` で成り立つなら、
  補助系なしで到達できる -/
  stability : ∀ {X Y Z₀ Z₁ : 𝒮},
    (∀ n : ℕ, prec (X + ((n : ℝ≥0) + 1)⁻¹ • Z₀) (Y + ((n : ℝ≥0) + 1)⁻¹ • Z₁)) → prec X Y
  /-- 組成：成分ごとの質量。複合で足し合わされ、スケーリングで `t` 倍される。 -/
  comp : 𝒮 →ₗ[ℝ≥0] (C → ℝ≥0)
  /-- 比較仮説 CH：組成が等しい二状態は少なくとも一方向に断熱到達できる -/
  comparison : ∀ {X Y}, comp X = comp Y → prec X Y ∨ prec Y X

namespace Adiabatic

variable {𝒮 C : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C]

@[inherit_doc] scoped infix:50 " ≺ " => Adiabatic.prec

/-- 断熱的同値 `X ∼ₐ Y` -/
def Equiv (X Y : 𝒮) : Prop := X ≺ Y ∧ Y ≺ X

@[inherit_doc] scoped infix:50 " ∼ₐ " => Adiabatic.Equiv

/-- 強い到達性 `X ≺≺ Y`：`X ≺ Y` だが `Y ≺ X` ではない (不可逆) -/
def StrictPrec (X Y : 𝒮) : Prop := X ≺ Y ∧ ¬ Y ≺ X

@[inherit_doc] scoped infix:50 " ≺≺ " => Adiabatic.StrictPrec

theorem prec_congr {X Y X' Y' : 𝒮} (h : X ≺ Y) (hX : X = X') (hY : Y = Y') : X' ≺ Y' :=
  hX ▸ hY ▸ h

theorem add_left (Z : 𝒮) {X Y : 𝒮} (h : X ≺ Y) : Z + X ≺ Z + Y := by
  simpa only [add_comm Z] using add_right Z h

theorem add_both {X Y X' Y' : 𝒮} (h : X ≺ Y) (h' : X' ≺ Y') : X + X' ≺ Y + Y' :=
  trans (add_right X' h) (add_left Y h')

omit [Adiabatic 𝒮 C] in
/-- A5 分割・再結合：`X` を `t : (1 - t)` に分けて並べた系は `X` と同値 (ここでは等しい)。 -/
theorem split_recombine (X : 𝒮) {t : ℝ≥0} (ht : t ≤ 1) : X = t • X + (1 - t) • X := by
  rw [← add_smul, add_tsub_cancel_of_le ht, one_smul]

/-- 相殺則 (Lieb–Yngvason Theorem 2.1)：共通の系 `Z` は取り除ける。A6 から従う。 -/
theorem cancel {X Y Z : 𝒮} (h : X + Z ≺ Y + Z) : X ≺ Y := by
  apply stability (Z₀ := Z) (Z₁ := Z)
  intro n
  set e : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹ with he
  have hs : e • X + e • Z ≺ e • Y + e • Z := by simpa only [smul_add] using smul e h
  -- `X/(n+1)` を一つずつ `Y/(n+1)` に置き換えていく
  have key : ∀ j : ℕ, j • (e • X) + e • Z ≺ j • (e • Y) + e • Z := by
    intro j
    induction j with
    | zero => simpa using refl (e • Z)
    | succ j ih =>
      have h1 : (j + 1) • (e • X) + e • Z ≺ j • (e • X) + (e • Y + e • Z) := by
        rw [succ_nsmul, add_assoc]
        exact add_left _ hs
      have h2 : j • (e • X) + e • Z + e • Y ≺ j • (e • Y) + e • Z + e • Y := add_right _ ih
      refine trans h1 (prec_congr h2 (by abel) (by rw [succ_nsmul]; abel))
  have hn : ∀ W : 𝒮, (n + 1) • (e • W) = W := by
    intro W
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul]
    have : ((n + 1 : ℕ) : ℝ≥0) * e = 1 := by
      rw [he]; push_cast; exact mul_inv_cancel₀ (by positivity)
    rw [this, one_smul]
  simpa only [hn] using key (n + 1)

/-- 基準状態。組成の等しい `X₀ ≺≺ X₁` と、組成 `k` ごとの基準状態 `ref k` (エントロピー `0`)。
`ref` は成分ごとに基準状態を一つ選び、組成に応じて並べたものにあたる。 -/
structure Calibration (𝒮 C : Type*) [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] [Adiabatic 𝒮 C] where
  /-- 組成ごとの基準状態 -/
  ref : (C → ℝ≥0) →ₗ[ℝ≥0] 𝒮
  comp_ref : ∀ k, comp (ref k) = k
  /-- エントロピー `0` の基準状態 -/
  X₀ : 𝒮
  /-- エントロピー `1` の基準状態 -/
  X₁ : 𝒮
  ref_X₀ : ref (comp X₀) = X₀
  comp_X₁ : comp X₁ = comp X₀
  strict : X₀ ≺≺ X₁

namespace Calibration

variable (c : Calibration 𝒮 C)

/-- 基準状態を混ぜた複合系 `(a X₀, b X₁)` -/
def Z (a b : ℝ≥0) : 𝒮 := a • c.X₀ + b • c.X₁

theorem Z_add (a b a' b' : ℝ≥0) : c.Z a b + c.Z a' b' = c.Z (a + a') (b + b') := by
  simp only [Z, add_smul]; abel

@[simp] theorem Z_zero : c.Z 0 0 = 0 := by simp [Z]

theorem smul_Z (t a b : ℝ≥0) : t • c.Z a b = c.Z (t * a) (t * b) := by
  simp [Z, smul_add, smul_smul]

theorem comp_Z (a b : ℝ≥0) : comp (c.Z a b) = (a + b) • comp c.X₀ := by
  simp [Z, c.comp_X₁, add_smul]

/-- `X` と同じ組成の基準状態 -/
def base (X : 𝒮) : 𝒮 := c.ref (comp X)

theorem base_add (X Y : 𝒮) : c.base (X + Y) = c.base X + c.base Y := by
  simp [base]

theorem base_smul (t : ℝ≥0) (X : 𝒮) : c.base (t • X) = t • c.base X := by
  simp [base]

theorem comp_base (X : 𝒮) : comp (c.base X) = comp X := c.comp_ref _

/-- 形式的な不等式 `P + α X₀ + β X₁ ≺ Q`。係数 `α, β` は負でもよく、負の部分は右辺に移して
読む。具体的には `P + a X₀ + b X₁ ≺ Q + a' X₀ + b' X₁` (`a - a' = α`, `b - b' = β`)
を満たす表示が存在することをいう。相殺則により表示の選び方によらない (`R.rep`)。 -/
def R (P Q : 𝒮) (α β : ℝ) : Prop :=
  ∃ a b a' b' : ℝ≥0, (a : ℝ) - a' = α ∧ (b : ℝ) - b' = β ∧ P + c.Z a b ≺ Q + c.Z a' b'

variable {c}

theorem exists_rep (α β : ℝ) :
    ∃ a b a' b' : ℝ≥0, (a : ℝ) - a' = α ∧ (b : ℝ) - b' = β :=
  ⟨α.toNNReal, β.toNNReal, (-α).toNNReal, (-β).toNNReal,
    by simp [Real.coe_toNNReal'],
    by simp [Real.coe_toNNReal']⟩

theorem R_congr {P Q : 𝒮} {α β α' β' : ℝ} (h : c.R P Q α β) (hα : α = α') (hβ : β = β') :
    c.R P Q α' β' := hα ▸ hβ ▸ h

/-- 表示の取り方によらない。 -/
theorem R.rep {P Q : 𝒮} {α β : ℝ} (h : c.R P Q α β) {a b a' b' : ℝ≥0}
    (ha : (a : ℝ) - a' = α) (hb : (b : ℝ) - b' = β) : P + c.Z a b ≺ Q + c.Z a' b' := by
  obtain ⟨a₀, b₀, a₀', b₀', ha₀, hb₀, h⟩ := h
  have e1 : a₀ + a' = a + a₀' := NNReal.eq (by push_cast; linarith)
  have e2 : b₀ + b' = b + b₀' := NNReal.eq (by push_cast; linarith)
  apply cancel (Z := c.Z a₀' b₀')
  refine prec_congr (add_right (c.Z a' b') h) ?_ (add_right_comm _ _ _)
  rw [add_assoc, add_assoc, c.Z_add, c.Z_add, e1, e2]

theorem R_of_rep {P Q : 𝒮} {a b a' b' : ℝ≥0} (h : P + c.Z a b ≺ Q + c.Z a' b') :
    c.R P Q ((a : ℝ) - a') ((b : ℝ) - b') := ⟨a, b, a', b', rfl, rfl, h⟩

theorem R_refl (P : 𝒮) : c.R P P 0 0 :=
  ⟨0, 0, 0, 0, by simp, by simp, refl _⟩

theorem prec_R_zero_add {P Q : 𝒮} {α β : ℝ} (h : c.R (0 + P) (0 + Q) α β) : c.R P Q α β := by
  simpa only [zero_add] using h

theorem R_of_prec {P Q : 𝒮} (h : P ≺ Q) : c.R P Q 0 0 :=
  ⟨0, 0, 0, 0, by simp, by simp, by simpa using h⟩

theorem R.to_prec {P Q : 𝒮} (h : c.R P Q 0 0) : P ≺ Q := by
  simpa using h.rep (a := 0) (b := 0) (a' := 0) (b' := 0) (by simp) (by simp)

theorem R.trans {P Q W : 𝒮} {α β α' β' : ℝ} (h : c.R P Q α β) (h' : c.R Q W α' β') :
    c.R P W (α + α') (β + β') := by
  obtain ⟨a, b, a', b', ha, hb, h⟩ := h
  obtain ⟨x, y, x', y', hx, hy, h'⟩ := h'
  refine ⟨a + x, b + y, a' + x', b' + y', by push_cast; linarith, by push_cast; linarith, ?_⟩
  have h1 := add_right (c.Z x y) h
  have h2 := add_right (c.Z a' b') h'
  refine prec_congr (Adiabatic.trans h1 (prec_congr h2 (add_right_comm _ _ _) rfl)) ?_ ?_
  · rw [add_assoc, c.Z_add]
  · rw [add_assoc, c.Z_add, add_comm x' a', add_comm y' b']

theorem R.add {P Q P' Q' : 𝒮} {α β α' β' : ℝ} (h : c.R P Q α β) (h' : c.R P' Q' α' β') :
    c.R (P + P') (Q + Q') (α + α') (β + β') := by
  obtain ⟨a, b, a', b', ha, hb, h⟩ := h
  obtain ⟨x, y, x', y', hx, hy, h'⟩ := h'
  refine ⟨a + x, b + y, a' + x', b' + y', by push_cast; linarith, by push_cast; linarith, ?_⟩
  refine prec_congr (add_both h h') ?_ ?_
  · rw [← c.Z_add]; abel
  · rw [← c.Z_add]; abel

theorem R.smul {P Q : 𝒮} {α β : ℝ} (h : c.R P Q α β) (t : ℝ≥0) :
    c.R (t • P) (t • Q) (t * α) (t * β) := by
  obtain ⟨a, b, a', b', ha, hb, h⟩ := h
  refine ⟨t * a, t * b, t * a', t * b', by push_cast; rw [← ha]; ring,
    by push_cast; rw [← hb]; ring, ?_⟩
  simpa only [smul_add, smul_Z] using Adiabatic.smul t h

/-- `γ ≥ 0` なら `γ X₀ ≺ γ X₁`。 -/
theorem R_base {γ : ℝ} (hγ : 0 ≤ γ) : c.R 0 0 γ (-γ) := by
  refine ⟨⟨γ, hγ⟩, 0, 0, ⟨γ, hγ⟩, by rw [NNReal.coe_zero, sub_zero]; rfl,
    by rw [NNReal.coe_zero, zero_sub]; rfl, ?_⟩
  simpa [Z] using Adiabatic.smul ⟨γ, hγ⟩ c.strict.1

/-- `R_base` に共通の系 `P` を添えたもの。 -/
theorem R_base' (P : 𝒮) {γ : ℝ} (hγ : 0 ≤ γ) : c.R P P γ (-γ) :=
  R_congr (prec_R_zero_add ((R_base hγ).add (R_refl P))) (by ring) (by ring)

/-- `γ < 0` だと `|γ| X₁ ≺ |γ| X₀` となり、`X₁ ≺ X₀` が出て矛盾する。 -/
theorem R_base_nonneg {P : 𝒮} {γ : ℝ} (h : c.R P P γ (-γ)) : 0 ≤ γ := by
  by_contra hγ'
  have hγ : γ < 0 := not_le.mp hγ'
  set g : ℝ≥0 := ⟨-γ, by linarith⟩
  have hg : (g : ℝ) = -γ := rfl
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0] at hg; simp at hg; linarith
  have h1 := h.rep (a := 0) (b := g) (a' := g) (b' := 0) (by rw [hg]; simp) (by rw [hg]; simp)
  have h2 : g • c.X₁ ≺ g • c.X₀ := by
    apply cancel (Z := P)
    simpa [Z, add_comm] using h1
  have h3 := Adiabatic.smul g⁻¹ h2
  rw [inv_smul_smul₀ hg0, inv_smul_smul₀ hg0] at h3
  exact c.strict.2 h3

/-- 補助の小さな量 `1/(n+1)` -/
noncomputable def ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem ε_pos (n : ℕ) : 0 < ε n := by unfold ε; positivity

/-- A6 の形式的な不等式への翻訳 (`X₀` を足し、`X₁` を引く方向)。 -/
theorem R.stability_up {P Q : 𝒮} {α β : ℝ} (h : ∀ n, c.R P Q (α + ε n) (β - ε n)) :
    c.R P Q α β := by
  obtain ⟨a, b, a', b', ha, hb⟩ := exists_rep α β
  refine ⟨a, b, a', b', ha, hb, ?_⟩
  apply stability (Z₀ := c.X₀) (Z₁ := c.X₁)
  intro n
  set e : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹ with he
  have hee : (e : ℝ) = ε n := by rw [he, ε]; push_cast; rfl
  have := (h n).rep (a := a + e) (b := b) (a' := a') (b' := b' + e)
    (by push_cast; rw [hee]; linarith) (by push_cast; rw [hee]; linarith)
  refine prec_congr this ?_ ?_
  · simp only [Z, add_smul]; abel
  · simp only [Z, add_smul]; abel

/-- A6 の形式的な不等式への翻訳 (`X₁` を足し、`X₀` を引く方向)。 -/
theorem R.stability_down {P Q : 𝒮} {α β : ℝ} (h : ∀ n, c.R P Q (α - ε n) (β + ε n)) :
    c.R P Q α β := by
  obtain ⟨a, b, a', b', ha, hb⟩ := exists_rep α β
  refine ⟨a, b, a', b', ha, hb, ?_⟩
  apply stability (Z₀ := c.X₁) (Z₁ := c.X₀)
  intro n
  set e : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹ with he
  have hee : (e : ℝ) = ε n := by rw [he, ε]; push_cast; rfl
  have := (h n).rep (a := a) (b := b + e) (a' := a' + e) (b' := b')
    (by push_cast; rw [hee]; linarith) (by push_cast; rw [hee]; linarith)
  refine prec_congr this ?_ ?_
  · simp only [Z, add_smul]; abel
  · simp only [Z, add_smul]; abel

variable (c)

/-- `Below X s`：形式的に `base X - s X₀ + s X₁ ≺ X`。 -/
def Below (X : 𝒮) (s : ℝ) : Prop := c.R (c.base X) X (-s) s

/-- `Above X s`：形式的に `X ≺ base X - s X₀ + s X₁`。 -/
def Above (X : 𝒮) (s : ℝ) : Prop := c.R X (c.base X) s (-s)

/-- エントロピー：同じ組成の基準状態から、`X₀` を `s` だけ `X₁` に置き換えた状態を
出発点にして `X` へ断熱到達できる `s` の上限。 -/
noncomputable def entropy (X : 𝒮) : ℝ := sSup {s | c.Below X s}

variable {c}

theorem below_le_above {X : 𝒮} {s s' : ℝ} (h : c.Below X s) (h' : c.Above X s') : s ≤ s' := by
  have := R_base_nonneg (R_congr (R.trans h h') (by ring) (by ring) :
    c.R (c.base X) (c.base X) (s' - s) (-(s' - s)))
  linarith

theorem Below.mono {X : 𝒮} {s s' : ℝ} (h : c.Below X s) (hs : s' ≤ s) : c.Below X s' :=
  R_congr ((R_base' (c.base X) (sub_nonneg.2 hs)).trans h) (by ring) (by ring)

theorem below_or_above (X : 𝒮) (s : ℝ) : c.Below X s ∨ c.Above X s := by
  obtain ⟨a, b, a', b', ha, hb⟩ := exists_rep (-s) s
  have hab : a + b = a' + b' := NNReal.eq (by push_cast; linarith)
  have hm : comp (c.base X + c.Z a b) = comp (X + c.Z a' b') := by
    simp only [map_add, comp_Z, comp_base, hab]
  rcases comparison hm with h | h
  · exact Or.inl ⟨a, b, a', b', ha, hb, h⟩
  · exact Or.inr ⟨a', b', a, b, by linarith, by linarith, h⟩

/-- 補助：`k = n + 1` 倍した関係を `1/k` 倍に戻すための計算 -/
theorem inv_mul_succ (n : ℕ) : ((n : ℝ≥0) + 1)⁻¹ * ((n : ℝ≥0) + 1) = 1 :=
  inv_mul_cancel₀ (by positivity)

/-- `X` より上の基準混合は必ず存在する (A6 と CH と `X₁ ⊀ X₀` から)。 -/
theorem exists_above (X : 𝒮) : ∃ s, c.Above X s := by
  by_contra hne
  simp only [not_exists] at hne
  have hb : ∀ s, c.Below X s := fun s => (below_or_above X s).resolve_right (hne s)
  apply c.strict.2
  apply stability (Z₀ := c.base X) (Z₁ := X)
  intro n
  set k : ℝ≥0 := (n : ℝ≥0) + 1
  have hk : k⁻¹ * k = 1 := inv_mul_succ n
  have h1 := (hb k).rep (a := 0) (b := k) (a' := k) (b' := 0) (by simp) (by simp)
  have h2 := Adiabatic.smul k⁻¹ h1
  refine prec_congr h2 ?_ ?_
  · rw [Z, zero_smul, zero_add, smul_add, smul_smul k⁻¹ k, hk, one_smul, add_comm]
  · rw [Z, zero_smul, add_zero, smul_add, smul_smul k⁻¹ k, hk, one_smul, add_comm]

/-- `X` より下の基準混合は必ず存在する。 -/
theorem exists_below (X : 𝒮) : ∃ s, c.Below X s := by
  by_contra hne
  simp only [not_exists] at hne
  have ha : ∀ s, c.Above X s := fun s => (below_or_above X s).resolve_left (hne s)
  apply c.strict.2
  apply stability (Z₀ := X) (Z₁ := c.base X)
  intro n
  set k : ℝ≥0 := (n : ℝ≥0) + 1
  have hk : k⁻¹ * k = 1 := inv_mul_succ n
  have h1 := (ha (-(k : ℝ))).rep (a := 0) (b := k) (a' := k) (b' := 0) (by simp) (by simp)
  have h2 := Adiabatic.smul k⁻¹ h1
  refine prec_congr h2 ?_ ?_
  · rw [Z, zero_smul, zero_add, smul_add, smul_smul k⁻¹ k, hk, one_smul, add_comm]
  · rw [Z, zero_smul, add_zero, smul_add, smul_smul k⁻¹ k, hk, one_smul, add_comm]

theorem bddAbove_below (X : 𝒮) : BddAbove {s | c.Below X s} := by
  obtain ⟨s', h'⟩ := exists_above (c := c) X
  exact ⟨s', fun s hs => below_le_above hs h'⟩

theorem nonempty_below (X : 𝒮) : {s | c.Below X s}.Nonempty := exists_below X

/-- 上限は達成される (A6)。 -/
theorem below_entropy (X : 𝒮) : c.Below X (c.entropy X) := by
  apply R.stability_up
  intro n
  have hlt : c.entropy X - ε n < sSup {s | c.Below X s} := by
    have := ε_pos n; unfold entropy; linarith
  obtain ⟨s, hs, hlt'⟩ := exists_lt_of_lt_csSup (nonempty_below X) hlt
  exact R_congr (Below.mono hs hlt'.le) (by ring) (by ring)

/-- `X ≺ (m - S) X₀ + S X₁` も成り立つ (CH と A6)。 -/
theorem above_entropy (X : 𝒮) : c.Above X (c.entropy X) := by
  apply R.stability_up
  intro n
  have hnb : ¬ c.Below X (c.entropy X + ε n) := by
    intro h
    have := le_csSup (bddAbove_below X) h
    have := ε_pos n
    unfold entropy at *; linarith
  exact R_congr ((below_or_above X _).resolve_left hnb) (by ring) (by ring)

/-- `X ∼ₐ (m - S) X₀ + S X₁` を満たす値はエントロピーに限る。 -/
theorem entropy_eq_of {X : 𝒮} {s : ℝ} (h : c.Below X s) (h' : c.Above X s) :
    c.entropy X = s :=
  le_antisymm (below_le_above (below_entropy X) h') (le_csSup (bddAbove_below X) h)

/-! ### エントロピーの測定：二分法

`S X` は上限として定義したが、実験の繰り返しで任意の精度で求められる。
一回の実験は、`base X` に基準状態の混合を添えた系から `X` へ断熱操作で移れるかを試すことである
(`Below X s`)。移れなければ CH により逆向きに移れる (`Above X s`)。
`test s = true` を「移れた」とすると、区間を半分にしていく二分法で、`n` 回の実験後に
`S X` を幅 `(b - a) / 2ⁿ` の区間に閉じ込められる (`entropy_bisect`)。 -/

theorem le_entropy {X : 𝒮} {s : ℝ} (h : c.Below X s) : s ≤ c.entropy X :=
  le_csSup (bddAbove_below X) h

theorem entropy_le {X : 𝒮} {s : ℝ} (h : c.Above X s) : c.entropy X ≤ s :=
  below_le_above (below_entropy X) h

/-- 二分法の一段：中点 `m` で実験し、結果に応じて区間の端を `m` に動かす。 -/
noncomputable def bisectStep (test : ℝ → Bool) (I : ℝ × ℝ) : ℝ × ℝ :=
  if test ((I.1 + I.2) / 2) then ((I.1 + I.2) / 2, I.2) else (I.1, (I.1 + I.2) / 2)

/-- **エントロピーの測定**：実験 `test` が、移れたとき `Below`、移れなかったとき `Above` を
与えるとする。`Below X a` と `Above X b` から始めた二分法の `n` 段目の区間 `[aₙ, bₙ]` は
`aₙ ≤ S X ≤ bₙ` かつ `bₙ - aₙ = (b - a) / 2ⁿ` を満たす。 -/
theorem entropy_bisect (X : 𝒮) (test : ℝ → Bool)
    (htrue : ∀ s, test s = true → c.Below X s) (hfalse : ∀ s, test s = false → c.Above X s)
    {a b : ℝ} (ha : c.Below X a) (hb : c.Above X b) (n : ℕ) :
    let J := (bisectStep test)^[n] (a, b)
    J.1 ≤ c.entropy X ∧ c.entropy X ≤ J.2 ∧ J.2 - J.1 = (b - a) / 2 ^ n := by
  suffices h : ∀ n, c.Below X ((bisectStep test)^[n] (a, b)).1 ∧
      c.Above X ((bisectStep test)^[n] (a, b)).2 ∧
      ((bisectStep test)^[n] (a, b)).2 - ((bisectStep test)^[n] (a, b)).1 = (b - a) / 2 ^ n by
    obtain ⟨h1, h2, h3⟩ := h n
    exact ⟨le_entropy h1, entropy_le h2, h3⟩
  intro n
  induction n with
  | zero => simpa using ⟨ha, hb⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    set J := (bisectStep test)^[n] (a, b)
    unfold bisectStep
    cases ht : test ((J.1 + J.2) / 2)
    · simp only [Bool.false_eq_true, ite_false]
      refine ⟨h1, hfalse _ ht, ?_⟩
      rw [pow_succ, ← div_div, ← h3]; ring
    · simp only [ite_true]
      refine ⟨htrue _ ht, h2, ?_⟩
      rw [pow_succ, ← div_div, ← h3]; ring

/-- **エントロピー原理**：組成の等しい状態について `X ≺ Y ↔ S X ≤ S Y`。 -/
theorem entropy_principle {X Y : 𝒮} (h : comp X = comp Y) :
    X ≺ Y ↔ c.entropy X ≤ c.entropy Y := by
  have hb : c.base X = c.base Y := by rw [base, base, h]
  constructor
  · intro hXY
    have : c.Below Y (c.entropy X) := by
      have := (below_entropy (c := c) X).trans (R_of_prec hXY)
      rw [hb] at this
      exact R_congr this (by ring) (by ring)
    exact below_le_above this (above_entropy Y)
  · intro hle
    have h1 := (above_entropy (c := c) X).trans (R_base' (c.base X) (sub_nonneg.2 hle))
    rw [hb] at h1
    exact (R_congr (h1.trans (below_entropy Y)) (by ring) (by ring)).to_prec

/-- 不可逆性：`X ≺≺ Y ↔ S X < S Y`。 -/
theorem strictPrec_iff {X Y : 𝒮} (h : comp X = comp Y) :
    X ≺≺ Y ↔ c.entropy X < c.entropy Y := by
  rw [StrictPrec, entropy_principle h, entropy_principle h.symm, not_le]
  exact ⟨fun h => h.2, fun h' => ⟨h'.le, h'⟩⟩

/-- **加法性** -/
theorem entropy_add (X Y : 𝒮) : c.entropy (X + Y) = c.entropy X + c.entropy Y := by
  apply entropy_eq_of
  · have := (below_entropy (c := c) X).add (below_entropy Y)
    rw [← base_add] at this
    exact R_congr this (by ring) rfl
  · have := (above_entropy (c := c) X).add (above_entropy Y)
    rw [← base_add] at this
    exact R_congr this rfl (by ring)

/-- **示量性** -/
theorem entropy_smul (t : ℝ≥0) (X : 𝒮) : c.entropy (t • X) = t * c.entropy X := by
  apply entropy_eq_of
  · have := (below_entropy (c := c) X).smul t
    rw [← base_smul] at this
    exact R_congr this (by ring) rfl
  · have := (above_entropy (c := c) X).smul t
    rw [← base_smul] at this
    exact R_congr this rfl (by ring)

/-- エントロピーは示量的な関数である。 -/
theorem entropy_extensive : IsExtensive c.entropy :=
  ⟨entropy_add, entropy_smul⟩

theorem base_X₀ : c.base c.X₀ = c.X₀ := c.ref_X₀

theorem base_X₁ : c.base c.X₁ = c.X₀ := by rw [base, c.comp_X₁, c.ref_X₀]

/-- 較正：`S X₀ = 0` -/
theorem entropy_X₀ : c.entropy c.X₀ = 0 := by
  apply entropy_eq_of
  · rw [Below, base_X₀]; exact R_congr (R_refl _) (by ring) rfl
  · rw [Above, base_X₀]; exact R_congr (R_refl _) rfl (by ring)

/-- 較正：`S X₁ = 1` -/
theorem entropy_X₁ : c.entropy c.X₁ = 1 := by
  apply entropy_eq_of
  · rw [Below, base_X₁]
    refine R_congr (R_of_rep (a := 0) (b := 1) (a' := 1) (b' := 0) ?_) (by simp) (by simp)
    simpa [Z, add_comm] using refl (c.X₀ + c.X₁)
  · rw [Above, base_X₁]
    refine R_congr (R_of_rep (a := 1) (b := 0) (a' := 0) (b' := 1) ?_) (by simp) (by simp)
    simpa [Z, add_comm] using refl (c.X₁ + c.X₀)

/-- **少量の補助系を添えても不可逆性は保たれる**：どの状態 `X` についても、`X` に `t X₁` を
添えた状態から、`t X₁` を `t X₀` に置き換えた状態へは断熱的に移れない (`t > 0` はいくら小さくてもよい)。
始状態 `X + t X₁` も `t` とともに動くので、これは「固定した状態の任意の近傍に到達できない状態がある」
という Carathéodory の原理そのものではない。その原理は公理から出ない (`model_reach_all`)。 -/
theorem caratheodory (X : 𝒮) {t : ℝ≥0} (ht : 0 < t) : ¬ (X + t • c.X₁ ≺ X + t • c.X₀) := by
  intro h
  have hc : comp (X + t • c.X₁) = comp (X + t • c.X₀) := by
    rw [map_add, map_add, map_smul, map_smul, c.comp_X₁]
  have := (c.entropy_principle hc).1 h
  rw [c.entropy_add, c.entropy_add, c.entropy_smul, c.entropy_smul, c.entropy_X₀,
    c.entropy_X₁] at this
  have : (0 : ℝ) < t := ht
  linarith

/-- **一意性**：示量的で、組成の等しい状態について `≺` を表現する関数 `S'` は、`a > 0` を使って
`a * S + S' ∘ base` と書ける。エントロピーの自由度は単位と、組成ごとの基準状態の値だけである。 -/
theorem entropy_unique (S' : 𝒮 → ℝ) (hS' : IsExtensive S')
    (hmono : ∀ X Y, comp X = comp Y → (X ≺ Y ↔ S' X ≤ S' Y)) :
    0 < S' c.X₁ - S' c.X₀ ∧
      ∀ X, S' X = (S' c.X₁ - S' c.X₀) * c.entropy X + S' (c.base X) := by
  have hZ : ∀ a b, S' (c.Z a b) = a * S' c.X₀ + b * S' c.X₁ := by
    intro a b; simp only [Z, hS'.1, hS'.2]
  refine ⟨?_, fun X => ?_⟩
  · have hm : comp c.X₀ = comp c.X₁ := c.comp_X₁.symm
    have h1 := (hmono _ _ hm).1 c.strict.1
    have h2 : ¬ S' c.X₁ ≤ S' c.X₀ := fun h => c.strict.2 ((hmono _ _ hm.symm).2 h)
    linarith [not_le.1 h2]
  · obtain ⟨a, b, a', b', ha, hb⟩ := exists_rep (-c.entropy X) (c.entropy X)
    have h1 := (below_entropy (c := c) X).rep ha hb
    have h2 := (above_entropy (c := c) X).rep (a := a') (b := b') (a' := a) (b' := b)
      (by linarith) (by linarith)
    have hab : a + b = a' + b' := NNReal.eq (by push_cast; linarith)
    have hm : comp (c.base X + c.Z a b) = comp (X + c.Z a' b') := by
      simp only [map_add, comp_Z, comp_base, hab]
    have heq := le_antisymm ((hmono _ _ hm).1 h1) ((hmono _ _ hm.symm).1 h2)
    rw [hS'.1, hS'.1, hZ, hZ] at heq
    have e1 : c.entropy X = (b : ℝ) - b' := hb.symm
    have e2 : -c.entropy X = (a : ℝ) - a' := ha.symm
    have e3 : (a : ℝ) - a' = -((b : ℝ) - b') := by linarith
    rw [e1]
    linear_combination (-1 : ℝ) * heq + S' c.X₀ * e3

end Calibration

end Adiabatic

end OpThermo
