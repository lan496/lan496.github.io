import OpThermo.Measurement

/-!
# 状態と平衡状態を実験の手順から定義する

「状態」も「平衡」も「時間」も原始概念にしない。原始概念は次の五つである (`Laboratory`)。
* `Prep`：準備手順。容器に物質を入れ、ピストンをある位置に固定する、といった具体的な手順。
* `Meas`：測定手順 (巨視的なもの)。体積の目盛りを読む、壁にかかる力を読む、など。
* `outcome p M`：準備手順 `p` の直後に測定手順 `M` を行ったときの読み。
* `Dur`：待ち手順。「砂時計の砂が落ち切るまで待つ」「振り子が 10 回振れるまで待つ」のように、
  基準となる過程が終わるまで待つという手順。数値の時間は使わない。
* `wait d p`：準備手順 `p` に待ち手順 `d` を続けた準備手順。

読みが実数で再現することは、ここで置く仮定である (測定誤差や確率的なばらつきは扱わない)。

## 定義

* `Indist p q`：どの測定手順でも、`p` と `q` の読みが一致する。
* `State`：区別できない準備手順の類。状態とは「測定手順で区別できない準備手順の集まり」である。
  測定手順の集まり `Meas` を広げれば、状態はより細かく分かれる。
* `IsStationary p`：どの待ち手順を続けても、どの読みも変わらない。

平衡の定義に数値の時間は要らない。どれだけ待っても変わらない、と言えれば足りる。

## 時間の目盛り (`Clock`)

数値の時間は、長さと同じ外延的構造から作る。
* 比較：二つの基準過程を同時に始め、`d` が `e` より遅れずに終わる。
* 連結：`d` が終わってから `e` を始める。待ちの言葉では `wait (d ∘ e) = wait e ∘ wait d`。

この比較と連結が外延的構造の法則を満たすことが、時間についての経験的仮定である。
そのとき時間の目盛りが単位を除いて一意に存在し (`Clock.time_exists`, `Clock.time_unique`)、
同じ比較と連結を与える二つの時計 (砂時計と振り子) の読みは比例する (`Clock.compatible`)。
「同時に始める」は、同じ場所で二つの出来事が一致することとして直接観測できるとする。

## 平衡状態を状態の性質にするための仮定

`IsStationary` は準備手順の性質であり、そのままでは状態の性質ではない。
同じ読みを与える二つの準備手順が、待ち手順を続けたあと別の読みを与えるかもしれないからである
(`stationary_not_state_property` がその例)。
そこで次の経験的仮定を明示する。
* `StateDeterminesEvolution`：区別できない準備手順は、待ち手順を続けた後も区別できない。

この仮定の下で、定常性は状態の性質になり (`stationary_congr`)、平衡状態
`IsEquilibrium` と平衡状態の集合 `EqState` が定義できる。
`FirstLaw.lean` と `Entropy.lean` の状態は、この `EqState` を念頭に置いている。
-/

namespace OpThermo

/-- 実験室で行える準備手順、測定手順、待ち手順。 -/
structure Laboratory where
  /-- 準備手順 -/
  Prep : Type*
  /-- 巨視的な測定手順 -/
  Meas : Type*
  /-- 準備手順 `p` の直後に測定手順 `M` を行ったときの読み -/
  outcome : Prep → Meas → ℝ
  /-- 待ち手順：基準となる過程 (砂時計、振り子の振動など) が終わるまで待つ -/
  Dur : Type*
  /-- 準備手順 `p` に待ち手順 `d` を続けた準備手順 -/
  wait : Dur → Prep → Prep

namespace Laboratory

variable (L : Laboratory)

/-- どの測定手順でも読みが一致する -/
def Indist (p q : L.Prep) : Prop := ∀ M, L.outcome p M = L.outcome q M

/-- 区別できないことによる同値関係 -/
def setoid : Setoid L.Prep where
  r := L.Indist
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h M => (h M).symm
      trans := fun h h' M => (h M).trans (h' M) }

/-- **状態**：測定手順で区別できない準備手順の類 -/
def State : Type _ := Quotient L.setoid

/-- 準備手順 `p` が作る状態 -/
def stateOf (p : L.Prep) : L.State := Quotient.mk L.setoid p

/-- どの待ち手順を続けても、どの読みも変わらない -/
def IsStationary (p : L.Prep) : Prop := ∀ d M, L.outcome (L.wait d p) M = L.outcome p M

/-- 経験的仮定：区別できない準備手順は、待ち手順を続けた後も区別できない。
「現在の状態が、何もしないときの以後の変化を決める」という主張である。 -/
def StateDeterminesEvolution : Prop :=
  ∀ p q d, L.Indist p q → L.Indist (L.wait d p) (L.wait d q)

variable {L}

/-- 仮定の下では、区別できない準備手順の一方が定常なら他方も定常。 -/
theorem stationary_congr (h : L.StateDeterminesEvolution) {p q : L.Prep} (hpq : L.Indist p q)
    (hp : L.IsStationary p) : L.IsStationary q := by
  intro d M
  rw [← h p q d hpq M, hp d M, hpq M]

variable (L)

/-- **平衡状態**：定常な準備手順で作られる状態。`StateDeterminesEvolution` の下で well-defined。 -/
def IsEquilibrium (h : L.StateDeterminesEvolution) : L.State → Prop :=
  Quotient.lift L.IsStationary fun _ _ hpq =>
    propext ⟨stationary_congr h hpq, stationary_congr h (L.setoid.iseqv.symm hpq)⟩

theorem isEquilibrium_stateOf (h : L.StateDeterminesEvolution) (p : L.Prep) :
    L.IsEquilibrium h (L.stateOf p) ↔ L.IsStationary p := Iff.rfl

/-- 平衡状態の集合 `Γ` -/
def EqState (h : L.StateDeterminesEvolution) : Type _ := {s : L.State // L.IsEquilibrium h s}

/-- **時計**：待ち手順の比較と連結が外延的構造をなす。
比較 `duration.le d e` は「二つの基準過程を同時に始めて、`d` が `e` より遅れずに終わる」、
連結 `duration.cat d e` は「`d` が終わってから `e` を始める」。 -/
structure Clock where
  /-- 待ち手順の比較と連結 -/
  duration : ExtensiveStructure L.Dur
  /-- 連結した待ちは、続けて待つことと同じ手順である -/
  wait_cat : ∀ d e p, L.wait (duration.cat d e) p = L.wait e (L.wait d p)

namespace Clock

variable {L} (C : L.Clock)

/-- 時間の目盛りの存在：単位の待ち手順 `u` (例えば振り子の一振り) に `1` を割り当てる
目盛り `τ` があり、比較を大小に、連結を和に移す。 -/
theorem time_exists (u : L.Dur) : ∃ τ : L.Dur → ℝ, C.duration.Represents τ ∧ τ u = 1 :=
  C.duration.length_exists u

/-- 時間の目盛りの一意性 -/
theorem time_unique (u : L.Dur) {τ τ' : L.Dur → ℝ} (h : C.duration.Represents τ)
    (h' : C.duration.Represents τ') (hu : τ u = 1) (hu' : τ' u = 1) : τ = τ' :=
  C.duration.length_unique u h h' hu hu'

/-- 同じ比較と連結を与える二つの時計の読みは比例する。 -/
theorem compatible {τA τB : L.Dur → ℝ} (hA : C.duration.Represents τA)
    (hB : C.duration.Represents τB) (u : L.Dur) : Compatible τA τB :=
  C.duration.compatible_of_represents hA hB u

include C in
/-- 定常な準備手順を待ち手順を続けて得た準備手順も定常である。 -/
theorem stationary_wait {p : L.Prep} (hp : L.IsStationary p) (d : L.Dur) :
    L.IsStationary (L.wait d p) := by
  intro e M
  rw [← C.wait_cat, hp, hp]

end Clock

end Laboratory

/-- 仮定 `StateDeterminesEvolution` を外すと、定常性は状態の性質でなくなる例。

準備手順は `0, 1, 2` の三つ、測定手順は一つ。`0` と `1` は直後の読みがどちらも `0` で区別できない。
`0` はどの待ち手順を続けても変わらないが、`1` は待ち手順を続けると `2` (読み `1`) に変わる。 -/
theorem stationary_not_state_property :
    ∃ (L : Laboratory.{0, 0, 0}) (p q : L.Prep),
      L.Indist p q ∧ L.IsStationary p ∧ ¬ L.IsStationary q := by
  let L : Laboratory.{0, 0, 0} :=
    { Prep := Fin 3
      Meas := Unit
      outcome := fun p _ => if p = 2 then 1 else 0
      Dur := Unit
      wait := fun _ p => if p = 1 then 2 else p }
  refine ⟨L, (0 : Fin 3), (1 : Fin 3), fun _ => by simp [L], fun d M => by simp [L], ?_⟩
  intro hq
  have := hq () ()
  simp [L] at this

end OpThermo
