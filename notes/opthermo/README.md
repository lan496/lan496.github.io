# OpThermo：操作主義による熱力学の Lean 4 形式化

長さの測定から出発し、断熱到達性でエントロピーを定義し、Gibbs 自由エネルギーの最小原理まで進む。
Lieb–Yngvason の公理化に沿う。
定義と、実験に基づいて新しく置く仮定 (公理) を、Lean の型で区別する。

## ビルドと検査

```sh
lake build                      # 全ファイルの型検査
lake env lean AxiomCheck.lean   # 主定理が依存する公理を表示
```

`AxiomCheck.lean` の出力は、どの主定理も `[propext, Classical.choice, Quot.sound]` だけである。
これはLeanとMathlibの標準の公理で、`sorry` や追加の公理は使っていない。
物理的な仮定は、すべて定理の仮定かクラスのフィールドとして明示してある。

## Blueprint

Leanのコードを読まなくても主張が分かるように、`blueprint/` に [leanblueprint](https://github.com/PatrickMassot/leanblueprint) 形式の解説を置いた。
各定義と定理を数式と日本語で述べ、対応するLeanの宣言名と、定理どうしの依存グラフを示す。

```sh
python3 scripts/build_figures.py               # blueprint/src/figures/ の図をPDFとSVGに変換
uvx --from leanblueprint leanblueprint web   # blueprint/web/ にHTMLを生成
uvx --from leanblueprint leanblueprint pdf   # blueprint/print/print.pdf を生成 (xelatex)
python3 scripts/build_site.py                # site/ に閲覧用ページをまとめる
```

`pygraphviz` のビルドにはHomebrewのgraphvizが要る。
その場合は `CFLAGS=-I/opt/homebrew/include LDFLAGS=-L/opt/homebrew/lib` を付けて実行する。

## 論理の鎖

| 段階 | ファイル | 主定理 | 物理的な仮定 |
|---|---|---|---|
| 長さ | `Measurement.lean` | `length_exists`, `length_unique`, `compatible_of_represents` | 棒の比較と連結が外延的構造をなす (全順序、結合性、可換性、単調性、正値性、アルキメデス性) |
| 状態、平衡状態、時間 | `States.lean` | `stationary_congr`, `stationary_not_state_property`, `Clock.time_exists`, `Clock.compatible` | 読みが再現すること、状態が以後の変化を決めること、待ち手順の比較と連結が外延的構造をなすこと |
| 仕事の力学的基礎 | `Mechanics.lean` | `gravity_work_eq`, `compatible_of_mechanicalLaw`, `compatible_with_balance` | 天秤が外延的構造をなすこと、仮想仕事の原理 |
| 内部エネルギー、熱 | `FirstLaw.lean` | `internalEnergy_spec`, `internalEnergy_unique`, `pathIndependent_iff_of_mechanicalLaw` | 断熱仕事の経路独立性、任意の二状態が一方向には断熱的に結べる |
| 相殺則 | `Entropy.lean` | `cancel` | A1–A4, A6 |
| 状態の空間 | `StateSpace.lean` | `IsExtensive` | 複合とスケーリングが加群をなすこと |
| エントロピー | `Entropy.lean` | `entropy_principle`, `strictPrec_iff`, `entropy_extensive`, `entropy_unique`, `entropy_bisect` (二分法による測定), `caratheodory` (少量の補助系を添えても不可逆。近傍の形の Carathéodory の原理は公理から出ない：`model_reach_all`) | A1–A6, 比較仮説 CH (組成の等しい状態), 基準状態 `X₀ ≺≺ X₁` と組成ごとの基準状態 |
| 公理の無矛盾性 | `Model.lean` | `model_entropy`, `model_reach_all` (近傍の Carathéodory の原理の反例) | なし (具体的なモデルを構成する) |
| 温度、圧力、化学ポテンシャル | `Temperature.lean` | `exchange_equilibrium`, `exchange_direction`, `fundamental_relation`, `fundamental_relation_multi`, `clausius`, `euler_homogeneous`, `temperature`, `temperature_pos`, `exchange_temperature`, `heat_flows_to_colder`, `contact_maximizes`, `entropy_calorimetry`, `idealGas_temperature`, `idealGas_law`, `idealGas_unique`, `fundamental_relation_forms`, `unattainability` | 微分可能性、平衡が全エントロピーの極大点であること |
| 断熱到達性と示量的な内部エネルギー | `Accessibility.lean` | `CompositeOps.toAdiabatic`, `CompositeOps.energy_spec`, `CompositeOps.energy_extensive` | A6 安定性と比較仮説、複合系の経路独立性、組成の保存 (化学反応なし) |
| Gibbs 自由エネルギー | `Gibbs.lean` | `gibbs_criterion`, `isolated_process_lowers_gibbs`, `reachable_of_gibbs_le`, `gibbs_euler`, `gibbs_large_reservoir`, `large_reservoir_criterion`, `gibbs_hasDerivAt` | エネルギーと体積の保存、溜めのエントロピーが一次式 (または大きな溜めの極限) |
| Helmholtz 自由エネルギーとエンタルピー | `Potentials.lean` | `helmholtz_criterion`, `CompositeOps.max_work`, `CompositeOps.enthalpy_change`, `joule_thomson`, `helmholtz_hasDerivAt`, `enthalpy_hasDerivAt`, `idealGas_enthalpy` | 理想的な熱浴、仕事をピストンの分とそれ以外に分けられること |
| エントロピーの凹性 | `Concavity.lean` | `Adiabatic.concaveOn_of_partition`, `concave_continuousOn`, `superadditive_of_concave` | 仕切りを抜いて座標の平均の状態に移れること |
| 熱容量 | `HeatCapacity.lean` | `heatCapacity_eq`, `heatCapacity_pos`, `entropy_hasDerivAt_temperature` | エントロピーの二階微分可能性 |

`gibbs_criterion` は `Entropy.lean` のエントロピー原理と加法性から直接証明している。
系と溜めの複合状態について、`X + R ≺ Y + R' ↔ G Y ≤ G X` が成り立つ。

## 形式化して分かった、元の文章の抜け

元の文章の流れは正しいが、Lean で証明を通すには次の点を補う必要があった。

1. 比較仮説は複合系に対して要る。
   §6.2 は単一の状態空間 `Γ` 上の比較可能性しか置いていない。
   しかし §7.4 の「`S(X) ≤ S(Y)` なら `X ≺ Y`」は、基準状態の混合 `((1-λ)X₀, λX₁)` と `X` の比較を使う。
   形式化では、組成の等しい任意の状態 (複合系を含む) の比較可能性を仮定した。
   この形にすると、§7.5 の加法性と示量性は追加の仮定なしに証明できる。

2. 上限が達成されるには A6 (安定性) が要る。
   §7.3 の `Z_{S(X)} ∼ X` は「適切な条件の下で」とだけ書かれている。
   必要なのはA6とCHである (`below_entropy`, `above_entropy`)。
   また `S(X)` が有限になること自体も、A6、CH、`X₁ ⊀ X₀` から示す必要がある (`exists_below`, `exists_above`)。

3. 相殺則 `(X, Z) ≺ (Y, Z) ⇒ X ≺ Y` が全体の要である。
   元の文章には現れないが、§7.2 の単調性の厳密な部分と、§7.4 の逆向きの議論はこれに依存する。
   相殺則はA6から導ける (`cancel`)。

4. 範囲 `X₀ ≺ X ≺ X₁` の外への拡張は不要だった。
   負の係数を右辺に移す形式的な不等式 `R` を使うと、すべての状態を一度に扱える。

5. 温度の導出には、平衡がエントロピー最大点であるという仮定が要る。
   §8.2 の「全エントロピーは減少しない、したがって平衡では `T_A = T_B`」は、そのままでは飛躍がある。
   エントロピー原理から出るのは、到達可能な変化で全エントロピーが減らないことだけである。
   平衡が最大点になるには、エネルギーの分配をどちら向きにも断熱的に変えられることを仮定する必要がある。

6. 「環境が十分大きいので `T₀, p₀` は変わらない」は極限の主張である。
   §11 の `ΔS_全体 = -ΔG/T₀` が等式で成り立つのは、溜めのエントロピーが `U, V` の一次式のときに限る。
   有限の溜めでは、示量性と微分可能性から、溜めを大きくする極限で `-ΔG/T₀` に収束する (`gibbs_large_reservoir`)。
   そのため判定は狭義の不等式でしか言えない。
   `ΔG < 0` なら十分大きな溜めで到達可能、`ΔG > 0` なら到達不可能で、`ΔG = 0` はこの議論では決まらない。

## 測定から量へ移るときの仮定

二つの目盛りが同じ量を測ることは、同じ数学的構造を持つことからは出ない。
そこで、そうした主張を定理の仮定として取り出した。

- 二つの目盛りが同じ量を測ることは、比例関係 `Compatible` として明示する。
  同じ比較と連結の構造を表現する目盛りどうしは、これを満たすことを証明した (`compatible_of_represents`)。
- 仕事に必要な力学は静力学だけである。
  仮想仕事の原理を満たす重みづけは天秤の質量に比例するものに限られる (`compatible_of_mechanicalLaw`)。
  慣性質量は使わないので、衝突実験の質量と天秤の質量の関係は問題にならない。
- 仕事は重りの質量と降下量の積の和 `Σ m h` で定め、重力加速度は使わない。
  重力が天秤の質量に比例するという仮定の下で、これは力学の仕事 `F · Δx` に一致する (`gravity_work_eq`)。
- 仕事の重みづけは、仮想仕事の原理を満たすものに限る。
  その範囲では、経路独立性 (第一法則) は重みづけの選び方によらない (`pathIndependent_iff_of_mechanicalLaw`)。
- 時間は数値として与えない。待ち手順 (砂時計が落ち切るまで待つ、など) を原始概念とし、平衡は「どの待ち手順を続けても読みが変わらない」と定義する。
  数値の時間は、待ち手順の比較 (同時に始めてどちらが先に終わるか) と連結 (続けて待つ) から、長さと同じ定理で作る (`Clock.time_exists`)。
- 定常性は、そのままでは状態の性質ではない (`stationary_not_state_property`)。
  状態が以後の変化を決めるという仮定を置いて初めて、平衡状態が定義できる。

型の選び方に隠れていて、まだ取り出していない仮定はblueprintの「残っている仮定」の章にまとめた。
例えば、読みが実数で再現すること、平衡状態の集合から複合系の空間を作る部分などである。

## 形式化していない部分

- Newton 力学 (慣性質量、力、運動方程式)。
  仕事は静力学 (天秤と仮想仕事の原理) だけから基礎づけた。
- 体積の幾何学的な定義 (§1.1)。
- 状態を `(U, V, N)` で座標づけできること、およびエントロピーの微分可能性 (§8.1)。
  Lieb–Yngvason はこれを単純系についての追加の公理から導くが、ここでは仮定として置いた。
- 異なる物質の間でのエントロピーの基準合わせ (§7.5 の末尾)、化学反応の平衡 (§12)。
  `entropy_unique` は単一の物質についての一意性 `S ↦ aS + bN` までを示す。

## 参考文献

全文の書誌情報はblueprintの参考文献の章にある。
主なものを挙げる。

- E. H. Lieb and J. Yngvason, The physics and mathematics of the second law of thermodynamics, Phys. Rep. 310, 1-96 (1999).
- E. H. Lieb and J. Yngvason, A guide to entropy and the second law of thermodynamics, Notices AMS 45, 571-581 (1998).
- E. H. Lieb and J. Yngvason, A fresh look at entropy and the second law of thermodynamics, Physics Today 53(4), 32-37 (2000).
- C. Carathéodory, Untersuchungen über die Grundlagen der Thermodynamik, Math. Ann. 67, 355-386 (1909).
- R. Giles, Mathematical Foundations of Thermodynamics, Pergamon (1964).
- A. Thess, The Entropy Principle: Thermodynamics for the Unsatisfied, Springer (2011).
- 田崎晴明『熱力学――現代的な視点から』培風館 (2000)。
- 佐々真一『熱力学入門』共立出版 (2000)。
- H. B. Callen, Thermodynamics and an Introduction to Thermostatistics, 2nd ed., Wiley (1985).
- O. Hölder, Die Axiome der Quantität und die Lehre vom Mass, Ber. Verh. Sächs. Ges. Wiss. Leipzig, Math.-Phys. Cl. 53, 1-64 (1901).
- D. H. Krantz, R. D. Luce, P. Suppes, and A. Tversky, Foundations of Measurement, Vol. I, Academic Press (1971).
- P. W. Bridgman, The Logic of Modern Physics, Macmillan (1927).
- L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming language, CADE-28, LNCS 12699, 625-635 (2021).
- The mathlib Community, The Lean mathematical library, CPP 2020, 367-381 (2020).
