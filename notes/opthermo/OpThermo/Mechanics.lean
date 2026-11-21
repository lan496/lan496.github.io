import OpThermo.Measurement

/-!
# 仕事の力学的な基礎：天秤とてこから「質量 × 降下量」へ

熱力学の仕事は、重りの上げ下げで測る。
ここで必要な力学は静力学だけであり、Newton の運動方程式や慣性質量は使わない。
原始概念は次のとおり。

* **重り**：系の外に置く固い物体で、天秤に載せられ、ひもで吊るせるもの。
  形や温度は変わらないものとし、状態は高さだけで指定される。
  仕事を受け渡すための道具であり、熱力学の系とは区別する。
* 重りの集まり `W` と天秤 (`balance : ExtensiveStructure W`)。
  比較は「天秤に載せてどちらに傾くか」、連結は「同じ皿に一緒に載せる」。
  `Measurement.lean` の定理により、天秤の質量目盛り `m` が単位を除いて一意に定まる。
* 降下の記録 `WeightDrops W`：どの重りが、どれだけ下がったか (上がれば負)。
  降下量は長さの目盛りで測る。
* `Feasible r`：てこや滑車などの純粋に力学的な装置 (手順の終わりには元の配置に戻る) で、
  降下の記録 `r` のとおりに重りを動かせる。

## 経験法則 (`MechanicalLaw m`)

重みづけ (重りの集まりの上の目盛り) `m : W → ℝ` を使った `Σ m(b) h` について、
* 力学的な装置だけで実現できる降下の記録では、`Σ m(b) h ≥ 0`
  (重りを全体として持ち上げる永久機関はない)。
* `Σ m(b) h = 0` となる降下の記録は、理想的な (摩擦のない) てこと滑車で実現できる。

これは仮想仕事の原理 (てこの原理) を操作の言葉で述べたものである。

## 主結果

* `mechanicalWork_zero_of_law`：法則を満たす重みづけは、`Σ m h = 0` となる記録の集まりで決まる。
* `compatible_of_mechanicalLaw`：法則を満たす正の重みづけは、互いに比例する
  (`Compatible`)。したがって、天秤の質量が法則を満たすなら (`hbal`)、
  力学的に意味のある仕事の重みづけは天秤の質量の定数倍に限られる。
  その定数は単位の選び方にあたる。

天秤の質量が法則を満たすこと自体は経験的な主張であり、仮定として明示する。
慣性質量 (衝突実験) と天秤の質量が比例するかは、ここでは使わない。
-/

namespace OpThermo

/-- **降下の記録**：どの重りが、どれだけ下がったかの一覧 `[(b₁, h₁), (b₂, h₂), …]`。
降下量 `h` は長さの目盛りで測り、上がった重りは負の降下量で表す。
例えば、Joule の実験で重り `b` が 0.5 m 下がったなら `[(b, 0.5)]`、
てこで `b` を `h_b` 下げて `u` を `h_u` 持ち上げたなら `[(b, h_b), (u, -h_u)]`。 -/
abbrev WeightDrops (W : Type*) : Type _ := List (W × ℝ)

/-- 重りの静力学。 -/
structure WeightStatics (W : Type*) where
  /-- 天秤：比較は傾きの向き、連結は同じ皿に載せること -/
  balance : ExtensiveStructure W
  /-- 純粋に力学的な装置で、降下の記録 `r` のとおりに重りを動かせる -/
  Feasible : WeightDrops W → Prop

/-- 降下の記録 `r` に対する `Σ m(b) h` (重みづけ `m`)。`g` 倍すると仕事になる。 -/
def mechanicalWork {W : Type*} (m : W → ℝ) (r : WeightDrops W) : ℝ :=
  (r.map fun bh => m bh.1 * bh.2).sum

/-! ### 力学の仕事 `F · Δx` との対応

力学では、一定の力 `F` の下で物体が変位 `Δx` だけ動くとき、力がした仕事を内積 `⟪F, Δx⟫` と定める。
重り `b` に働く重力は鉛直下向きで大きさ `m(b) g` なので、重力がした仕事は `m(b) g` と
鉛直下向きの変位 (降下量) の積になる。水平方向の動きは寄与しない。 -/

/-- 三次元の空間 -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- 鉛直下向きの単位ベクトル：吊るした重りが静止したときにひもが指す向き (第三座標を上向きにとる) -/
noncomputable def down : Space := EuclideanSpace.single 2 (-1)

/-- 力学の仕事：一定の力 `F` の下で変位 `Δx` だけ動くときの仕事 `⟪F, Δx⟫` -/
noncomputable def forceWork (F Δx : Space) : ℝ := inner ℝ F Δx

/-- 重り (天秤の目盛り `m`) に働く重力 `m g ↓`：吊るした重りがひもを引く力。
天秤は重りがひもを引く強さを比べる手順なので、大きさは天秤の目盛りに比例する。
`g` は、力を天秤とは別の単位で表すときの換算係数。 -/
noncomputable def gravity (m g : ℝ) : Space := (m * g) • down

/-- 変位 `Δx` の鉛直下向きの成分 (降下量) -/
noncomputable def descent (Δx : Space) : ℝ := inner ℝ down Δx

/-- 重力がした仕事は `m g × 降下量`。水平方向の変位は寄与しない。 -/
theorem forceWork_gravity (m g : ℝ) (Δx : Space) :
    forceWork (gravity m g) Δx = m * g * descent Δx := by
  simp [forceWork, gravity, descent, real_inner_smul_left]

/-- 重りの変位の一覧から降下の記録を作る -/
noncomputable def dropsOf {W : Type*} (l : List (W × Space)) : WeightDrops W :=
  l.map fun bx => (bx.1, descent bx.2)

/-- **力学の仕事との一致**：重りたちに重力がした仕事の和 `Σ ⟪m(b) g ↓, Δx_b⟫` は、
降下の記録から計算した `g Σ m(b) h` に等しい。 -/
theorem gravity_work_eq {W : Type*} (m : W → ℝ) (g : ℝ) (l : List (W × Space)) :
    (l.map fun bx => forceWork (gravity (m bx.1) g) bx.2).sum =
      g * mechanicalWork m (dropsOf l) := by
  induction l with
  | nil => simp [mechanicalWork, dropsOf]
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, forceWork_gravity] at ih ⊢
    simp only [mechanicalWork, dropsOf, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

namespace WeightStatics

variable {W : Type*} (S : WeightStatics W)

/-- 重みづけ `m` についての力学の経験法則 (仮想仕事の原理)。 -/
def MechanicalLaw (m : W → ℝ) : Prop :=
  (∀ r, S.Feasible r → 0 ≤ mechanicalWork m r) ∧ (∀ r, mechanicalWork m r = 0 → S.Feasible r)

/-- 記録の向きを逆にする (下がった重りを上げ、上がった重りを下げる)。 -/
def reverse (r : WeightDrops W) : WeightDrops W := r.map fun bh => (bh.1, -bh.2)

theorem mechanicalWork_reverse (m : W → ℝ) (r : WeightDrops W) :
    mechanicalWork m (reverse r) = -mechanicalWork m r := by
  induction r with
  | nil => simp [mechanicalWork, reverse]
  | cons x r ih =>
    simp only [mechanicalWork, reverse, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

variable {S}

/-- 法則を満たす二つの重みづけは、釣り合う降下の記録 (`Σ m h = 0`) の集まりが一致する。 -/
theorem mechanicalWork_zero_of_law {m m' : W → ℝ} (h : S.MechanicalLaw m)
    (h' : S.MechanicalLaw m') {r : WeightDrops W} (hr : mechanicalWork m r = 0) :
    mechanicalWork m' r = 0 := by
  have f1 := h'.1 r (h.2 r hr)
  have hrev : mechanicalWork m (reverse r) = 0 := by rw [mechanicalWork_reverse, hr, neg_zero]
  have f2 := h'.1 _ (h.2 _ hrev)
  rw [mechanicalWork_reverse] at f2
  linarith

/-- **仕事の重みづけの一意性**：力学の法則を満たす正の重みづけは互いに比例する。 -/
theorem compatible_of_mechanicalLaw {m m' : W → ℝ} (h : S.MechanicalLaw m)
    (h' : S.MechanicalLaw m') (hpos : ∀ b, 0 < m b) (hpos' : ∀ b, 0 < m' b) (u : W) :
    Compatible m m' := by
  refine ⟨m' u / m u, div_pos (hpos' u) (hpos u), fun b => ?_⟩
  -- 重り `b` を `m u` だけ下げ、`u` を `m b` だけ上げる降下の記録は `m` で釣り合う
  have hr : mechanicalWork m [(b, m u), (u, -m b)] = 0 := by
    simp [mechanicalWork]; ring
  have := mechanicalWork_zero_of_law h h' hr
  simp [mechanicalWork] at this
  have hu := hpos u
  field_simp
  linarith

/-- 天秤の質量目盛りが力学の法則を満たすなら (経験的仮定 `hbal`)、法則を満たす任意の正の
重みづけは天秤の質量に比例する。仕事 `Σ m h` の `m` は天秤で測った質量でよく、
比例定数は単位の選び方にあたる。 -/
theorem compatible_with_balance {mbal m : W → ℝ} (hrep : S.balance.Represents mbal)
    (hbal : S.MechanicalLaw mbal) (h : S.MechanicalLaw m) (hpos : ∀ b, 0 < m b) (u : W) :
    Compatible mbal m :=
  compatible_of_mechanicalLaw hbal h hrep.pos hpos u

end WeightStatics

end OpThermo
