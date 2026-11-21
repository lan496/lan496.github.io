import Mathlib

/-!
# 状態の空間と示量的な関数

状態の全体 `𝒮` は、複合 (`X + Y`) とスケーリング (`t • X`, `t : ℝ≥0`) を持つ `ℝ≥0` 加群とする。
`X + Y` は二つの系を仕切りで隔てて並べた複合系、`t • X` は仕切りで分けた (または増やした) 系である。
加群の等式は、両辺の準備手順が同じ状態を与えるという仮定である。

`𝒮` 上の実数値関数が示量的であるとは、複合で足し合わされ、スケーリングで `t` 倍されることをいう。
系の組成 (成分ごとの質量)、内部エネルギー、エントロピーはどれも示量的である。
-/

open NNReal

namespace OpThermo

/-- **示量的な関数**：`f (X + Y) = f X + f Y` かつ `f (t • X) = t * f X`。 -/
def IsExtensive {𝒮 : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] (f : 𝒮 → ℝ) : Prop :=
  (∀ X Y, f (X + Y) = f X + f Y) ∧ ∀ (t : ℝ≥0) X, f (t • X) = t * f X

theorem IsExtensive.map_zero {𝒮 : Type*} [AddCommMonoid 𝒮] [Module ℝ≥0 𝒮] {f : 𝒮 → ℝ}
    (h : IsExtensive f) : f 0 = 0 := by
  simpa using h.2 0 0

end OpThermo
