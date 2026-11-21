import OpThermo.Mechanics

/-!
# 第一法則：断熱仕事から内部エネルギーを構成する

断熱操作とは、外界に残る正味の変化が重りの高さの変化だけである操作をいう。
その断熱操作で重りが失った力学的エネルギー (`m h` の減少) を、系になされた仕事 `work p`
として測る。

## 経験的仮定 (`AdiabaticProcesses`)

* 断熱操作は続けて実行でき、仕事は足し合わされる (`comp`, `work_comp`)。
* **経路独立性** (Joule)：同じ始状態・終状態を結ぶ断熱操作の仕事は等しい (`path_indep`)。
* **連結性**：任意の二状態は、少なくとも一方向に断熱操作で結べる (`connected`)。

## 主結果

* `exists_internalEnergy`：`U Y - U X = work p` (`p : X → Y` は任意の断熱操作) を満たす
  状態関数 `U` が存在する。
* `internalEnergy_unique`：そのような `U` は定数の差を除いて一意。
* `heat` と `first_law`：断熱とは限らない手順の熱を `Q := ΔU - W` と定義すると `ΔU = Q + W`。
  `heat_adiabatic`：断熱操作の熱は `0` である (定義の整合性)。

## 仕事の計算に使う重みづけを明示する (`AdiabaticOps`)

仕事の力学的な意味は `Mechanics.lean` で与える。
ここでの仕事は降下の記録に対する `Σ m h` であり (`Mechanics.gravity_work_eq` により、重力がした力学の仕事を `g` で割ったもの)、
`pathIndependent_iff_of_mechanicalLaw` により、力学の法則を満たす重みづけのどれを選んでも
経路独立性 (第一法則) の内容は変わらない。


`AdiabaticProcesses` は仕事を一つの実数として受け取るので、仕事をどう測ったかが隠れる。
`AdiabaticOps` では、各断熱操作に降下の記録 (どの重りがどれだけ下がったか) だけを持たせ、
仕事 `Σ m(b) h` は重みづけ `m` を与えて初めて計算する。

* `AdiabaticOps.PathIndependent m`：経路独立性は `m` を明示した経験的仮定になる。
* `pathIndependent_iff_of_compatible`：両立する (比例する) 重みづけの間では、
  経路独立性は同時に成り立つか同時に成り立たない。
* `internalEnergy_of_compatible`：そのとき内部エネルギーは `U_B = c U_A + d`。
* `pathIndependent_depends_on_mass`：両立しない重みづけでは、片方で経路独立性が成り立ち
  もう片方で破れる例がある。どの重みづけで第一法則を検証したかは、省略できない情報である。
-/

namespace OpThermo

/-- 平衡状態の集合 `Γ` 上の断熱操作と、その仕事。
`Γ` には `States.lean` の `Laboratory.EqState` (定常な準備手順で作られる状態) を想定する。 -/
structure AdiabaticProcesses (Γ : Type*) where
  /-- `Operation X Y` は、平衡状態 `X` から平衡状態 `Y` へ移す断熱操作の集まり (型) である。
  その一つ一つの要素 `p : Operation X Y` が、装置と手順を指定した一つの断熱操作である。
  空なら `X` から `Y` へ断熱的には移せない。 -/
  Operation : Γ → Γ → Type*
  /-- 断熱操作の間に外界の重りが失った力学的エネルギー (系になされた仕事) -/
  work : ∀ {X Y}, Operation X Y → ℝ
  /-- 二つの断熱操作を続けて行う -/
  comp : ∀ {X Y Z}, Operation X Y → Operation Y Z → Operation X Z
  work_comp : ∀ {X Y Z} (p : Operation X Y) (q : Operation Y Z), work (comp p q) = work p + work q
  /-- 経路独立性 -/
  path_indep : ∀ {X Y} (p q : Operation X Y), work p = work q
  /-- 連結性 -/
  connected : ∀ X Y, Nonempty (Operation X Y) ∨ Nonempty (Operation Y X)

namespace AdiabaticProcesses

variable {Γ : Type*} (A : AdiabaticProcesses Γ)

/-- 閉じた断熱操作の仕事は `0`。 -/
theorem work_loop {X : Γ} (p : A.Operation X X) : A.work p = 0 := by
  have := A.work_comp p p
  rw [A.path_indep (A.comp p p) p] at this
  linarith

/-- 基準状態 `X₀` に対する内部エネルギー。`X₀ → X` の断熱操作があればその仕事、
なければ `X → X₀` の断熱操作の仕事の符号を変えたもの。 -/
noncomputable def internalEnergy (X₀ : Γ) (X : Γ) : ℝ := by
  classical
  exact if h : Nonempty (A.Operation X₀ X) then A.work h.some
    else -A.work ((A.connected X₀ X).resolve_left h).some

/-- **内部エネルギーの存在**：任意の断熱操作 `p : X → Y` で `U Y - U X = work p`。 -/
theorem internalEnergy_spec (X₀ : Γ) {X Y : Γ} (p : A.Operation X Y) :
    A.internalEnergy X₀ Y - A.internalEnergy X₀ X = A.work p := by
  classical
  unfold internalEnergy
  split_ifs with hY hX hX
  · -- X₀ → X → Y と X₀ → Y
    have := A.work_comp hX.some p
    rw [A.path_indep (A.comp hX.some p) hY.some] at this
    linarith
  · -- X → X₀ → Y
    set a := ((A.connected X₀ X).resolve_left hX).some
    have := A.work_comp a hY.some
    rw [A.path_indep (A.comp a hY.some) p] at this
    linarith
  · -- X₀ → X → Y → X₀ は閉じた断熱操作
    set b := ((A.connected X₀ Y).resolve_left hY).some
    have h1 := A.work_loop (A.comp (A.comp hX.some p) b)
    rw [A.work_comp, A.work_comp] at h1
    linarith
  · -- X → Y → X₀ と X → X₀
    set a := ((A.connected X₀ X).resolve_left hX).some
    set b := ((A.connected X₀ Y).resolve_left hY).some
    have := A.work_comp p b
    rw [A.path_indep (A.comp p b) a] at this
    linarith

theorem exists_internalEnergy [Nonempty Γ] :
    ∃ U : Γ → ℝ, ∀ {X Y : Γ} (p : A.Operation X Y), U Y - U X = A.work p :=
  ⟨A.internalEnergy (Classical.arbitrary Γ), fun p => A.internalEnergy_spec _ p⟩

/-- **一意性**：断熱仕事を再現する状態関数は、定数の差を除いて一意。 -/
theorem internalEnergy_unique (U U' : Γ → ℝ)
    (hU : ∀ {X Y : Γ} (p : A.Operation X Y), U Y - U X = A.work p)
    (hU' : ∀ {X Y : Γ} (p : A.Operation X Y), U' Y - U' X = A.work p) (X₀ : Γ) :
    ∀ X, U' X = U X + (U' X₀ - U X₀) := by
  intro X
  rcases A.connected X₀ X with h | h
  · obtain ⟨p⟩ := h
    have := hU p; have := hU' p; linarith
  · obtain ⟨p⟩ := h
    have := hU p; have := hU' p; linarith

/-- 断熱とは限らない手順で入った熱：`Q := ΔU - W`。 -/
def heat (U : Γ → ℝ) (X Y : Γ) (W : ℝ) : ℝ := U Y - U X - W

/-- **第一法則** `ΔU = Q + W` (熱の定義そのもの)。 -/
theorem first_law (U : Γ → ℝ) (X Y : Γ) (W : ℝ) : U Y - U X = heat U X Y W + W := by
  unfold heat; ring

/-- 断熱操作で入る熱は `0`。熱の定義が断熱操作の定義と矛盾しないことを示す。 -/
theorem heat_adiabatic (U : Γ → ℝ) (hU : ∀ {X Y : Γ} (p : A.Operation X Y), U Y - U X = A.work p)
    {X Y : Γ} (p : A.Operation X Y) : heat U X Y (A.work p) = 0 := by
  unfold heat; rw [hU p]; ring

end AdiabaticProcesses

/-- 断熱操作と、その降下の記録。仕事はまだ数として持たせない。
断熱操作とは、系を平衡状態 `X` から `Y` へ移す手順で、終わったとき使った装置がすべて元の状態に戻り、
系の外に残る変化が重りの高さだけであるもの。熱という語は使わない。
どの手順がこの条件を満たすかの判定は形式化しておらず、`Operation X Y` を与えられたものとする。
仕事は、降下の記録に重みづけを当てはめて計算する (`work`)。 -/
structure AdiabaticOps (Γ : Type*) (Weight : Type*) where
  /-- `Operation X Y`：平衡状態 `X` から `Y` へ移す断熱操作の集まり。要素一つが、装置と手順を指定した一つの断熱操作。 -/
  Operation : Γ → Γ → Type*
  /-- 二つの断熱操作を続けて行う -/
  comp : ∀ {X Y Z}, Operation X Y → Operation Y Z → Operation X Z
  /-- 断熱操作 `p` の降下の記録：`p` の間に、どの重りがどれだけ下がったか -/
  drops : ∀ {X Y}, Operation X Y → WeightDrops Weight
  /-- 続けて行った断熱操作の降下の記録は、それぞれの記録をつなげたもの -/
  drops_comp : ∀ {X Y Z} (p : Operation X Y) (q : Operation Y Z),
    drops (comp p q) = drops p ++ drops q
  /-- 連結性 -/
  connected : ∀ X Y, Nonempty (Operation X Y) ∨ Nonempty (Operation Y X)

namespace AdiabaticOps

variable {Γ Weight : Type*} (O : AdiabaticOps Γ Weight)

/-- **断熱到達性** `X ≺ Y`：`X` から `Y` への断熱操作が存在する。 -/
def Prec (X Y : Γ) : Prop := Nonempty (O.Operation X Y)

/-- 連結性は、断熱到達性で任意の二状態が比べられることと同じ。 -/
theorem prec_total (X Y : Γ) : O.Prec X Y ∨ O.Prec Y X := O.connected X Y

/-- **仕事**：断熱操作 `p` の降下の記録から計算した `Σ m(b) h`。
単位は「重みづけの単位の重りを単位の長さだけ下げる仕事」であり、重力加速度は使わない。
ジュールに換算するときだけ、重力加速度 `g` を掛ける。
仕事は断熱操作の関数であり、平衡状態の関数ではない。 -/
def work (m : Weight → ℝ) {X Y : Γ} (p : O.Operation X Y) : ℝ :=
  mechanicalWork m (O.drops p)

theorem work_comp (m : Weight → ℝ) {X Y Z : Γ} (p : O.Operation X Y) (q : O.Operation Y Z) :
    O.work m (O.comp p q) = O.work m p + O.work m q := by
  simp [work, mechanicalWork, O.drops_comp]

/-- 経路独立性 (Joule)。どの重みづけ `m` で仕事を計算したかを明示する。 -/
abbrev PathIndependent (m : Weight → ℝ) : Prop :=
  ∀ {X Y : Γ} (p q : O.Operation X Y), O.work m p = O.work m q

/-- 経路独立性が成り立つ重みづけを選べば、仕事を一つの実数として扱える。 -/
def toProcesses (m : Weight → ℝ) (h : O.PathIndependent m) :
    AdiabaticProcesses Γ where
  Operation := O.Operation
  work := O.work m
  comp := O.comp
  work_comp := O.work_comp m
  path_indep := h
  connected := O.connected

/-- 重みづけ `m` で測った断熱仕事から構成した内部エネルギー (基準状態 `X₀`)。 -/
noncomputable def energy (m : Weight → ℝ) (h : O.PathIndependent m) (X₀ : Γ) :
    Γ → ℝ :=
  (O.toProcesses m h).internalEnergy X₀

theorem energy_spec (m : Weight → ℝ) (h : O.PathIndependent m) (X₀ : Γ) {X Y : Γ}
    (p : O.Operation X Y) : O.energy m h X₀ Y - O.energy m h X₀ X = O.work m p :=
  (O.toProcesses m h).internalEnergy_spec X₀ p

theorem work_of_compatible {mA mB : Weight → ℝ} {c : ℝ} (hc : ∀ b, mB b = c * mA b)
    {X Y : Γ} (p : O.Operation X Y) : O.work mB p = c * O.work mA p := by
  unfold work mechanicalWork
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro bh _
  rw [hc]; ring

/-- 両立する重みづけの間では、経路独立性は同値。 -/
theorem pathIndependent_iff_of_compatible {mA mB : Weight → ℝ} (h : Compatible mA mB) :
    O.PathIndependent mA ↔ O.PathIndependent mB := by
  obtain ⟨c, hc0, hc⟩ := h
  constructor
  · intro hA X Y p q
    rw [O.work_of_compatible hc, O.work_of_compatible hc, hA p q]
  · intro hB X Y p q
    have := hB p q
    rw [O.work_of_compatible hc, O.work_of_compatible hc] at this
    exact mul_left_cancel₀ hc0.ne' this

/-- 力学の法則 (`Mechanics.lean`) を満たす二つの正の重みづけの間では、経路独立性は同値。
第一法則は、力学的に意味のある仕事の測り方のどれを選んでも同じ内容になる。 -/
theorem pathIndependent_iff_of_mechanicalLaw (S : WeightStatics Weight) {mA mB : Weight → ℝ}
    (hA : S.MechanicalLaw mA) (hB : S.MechanicalLaw mB) (posA : ∀ b, 0 < mA b)
    (posB : ∀ b, 0 < mB b) (u : Weight) :
    O.PathIndependent mA ↔ O.PathIndependent mB :=
  O.pathIndependent_iff_of_compatible
    (WeightStatics.compatible_of_mechanicalLaw hA hB posA posB u)

/-- 両立する重みづけから作った内部エネルギーは、`U_B = c U_A + d` の関係にある。 -/
theorem internalEnergy_of_compatible {mA mB : Weight → ℝ} {c : ℝ} (hc : ∀ b, mB b = c * mA b)
    (hA : O.PathIndependent mA) (hB : O.PathIndependent mB) (X₀ : Γ) :
    ∃ d : ℝ, ∀ X, (O.toProcesses mB hB).internalEnergy X₀ X =
      c * (O.toProcesses mA hA).internalEnergy X₀ X + d := by
  refine ⟨_, (O.toProcesses mB hB).internalEnergy_unique
    (fun X => c * (O.toProcesses mA hA).internalEnergy X₀ X) _ ?_ ?_ X₀⟩
  · intro X Y p
    have := (O.toProcesses mA hA).internalEnergy_spec X₀ p
    have h2 : O.work mB (X := X) (Y := Y) p = c * O.work mA p := O.work_of_compatible hc p
    change c * _ - c * _ = O.work mB p
    rw [h2, ← mul_sub]
    exact congrArg (c * ·) this
  · intro X Y p
    exact (O.toProcesses mB hB).internalEnergy_spec X₀ p

end AdiabaticOps

/-- 重みづけが両立しないと、経路独立性は手続きに依存しうる。

状態は一つだけで、断熱操作は「重り A を 1 下げ、重り B を 1 上げる」を何回か繰り返すもの。
両方の重りに質量 `1` を割り当てる測定では仕事は常に `0` で、経路独立性が成り立つ。
重り B に質量 `2` を割り当てる測定では、1 回の断熱操作の仕事が `-1` になり、
何もしない断熱操作 (仕事 `0`) と食い違う。 -/
theorem pathIndependent_depends_on_mass :
    ∃ (O : AdiabaticOps.{0, 0, 0} Unit Bool) (mA mB : Bool → ℝ),
      O.PathIndependent mA ∧ ¬ O.PathIndependent mB := by
  let O : AdiabaticOps Unit Bool :=
    { Operation := fun _ _ => List Unit
      comp := fun p q => p ++ q
      drops := fun p => p.flatMap fun _ => [(true, 1), (false, -1)]
      drops_comp := fun p q => List.flatMap_append
      connected := fun _ _ => Or.inl ⟨[]⟩ }
  have hwork : ∀ (m : Bool → ℝ) (p : List Unit),
      O.work m (X := ()) (Y := ()) p = p.length * (m true - m false) := by
    intro m p
    induction p with
    | nil => simp [AdiabaticOps.work, mechanicalWork, O]
    | cons a p ih =>
      simp only [AdiabaticOps.work, mechanicalWork, O, List.flatMap_cons, List.map_append,
        List.sum_append, List.length_cons] at ih ⊢
      rw [ih]; push_cast; simp; ring
  refine ⟨O, fun _ => 1, fun b => if b then 1 else 2, ?_, ?_⟩
  · intro X Y p q
    rw [hwork, hwork]; simp
  · intro h
    have := h (X := ()) (Y := ()) [()] []
    rw [hwork, hwork] at this
    norm_num at this

end OpThermo
