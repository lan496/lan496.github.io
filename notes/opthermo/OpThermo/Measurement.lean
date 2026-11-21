import Mathlib

/-!
# 長さは測れる：比較と連結から実数値の目盛りへ

棒に対して行う手順は二つだけである。
* 連結 `cat a b`：棒 `a` と `b` を端と端でつなぐ。
* 比較 `le a b`：二本の棒の一端をそろえて並べ、`a` の他端が `b` の他端を越えない。

棒そのものの集まり `A` と、この二つの手順を原始概念とする (`ExtensiveStructure`)。
「長さ」という量は仮定せず、手順の結果についての経験法則だけを置く。
同じ形の構造は、天秤の比較と皿への同時載せによる質量にも使える。

## 経験的仮定 (外延的構造。Krantz–Luce–Suppes–Tversky の Definition 3.1 に相当)

* 比較は全順序的で推移的 (`le_total`, `le_trans`)。
* 連結は、比較で区別できない範囲で結合的・可換 (`cat_assoc`, `cat_comm`)。
* 単調性：同じ棒を継ぎ足しても比較の結果は変わらない (`mono`)。
* 正値性：棒を継ぎ足すと、元の棒より長くなる (`pos`)。
* アルキメデス性：`a` が `b` より長ければ、十分多くつないだ `a` は、
  どんな差も追い越す (`arch`)。

## 主結果

* `length_exists`：比較を大小に、連結を和に移す目盛り `ℓ : A → ℝ` で、
  単位の棒 `u` に `1` を割り当てるものが存在する (Hölder の定理)。値は正。
* `length_unique`：単位を固定すれば、そのような目盛りは一つしかない。
* `compatible_of_represents`：同じ構造を表現する二つの目盛りは比例する (`Compatible`)。

## 存在の証明の流れ

比較で区別できない棒を同一視した商 `Q` は、全順序を持つ可換半群になる。
`Q × Q` の形式的な差で群 `G` を作り、順序とアルキメデス性を移す。
`G` は Mathlib の `Archimedean.embedReal` で `ℝ` に埋め込める。
-/

open Function

namespace OpThermo

/-- アルキメデス的な全順序アーベル群は、単位 `u > 0` を `1` に移す順序加法準同型で
`ℝ` に埋め込める (Hölder の定理。Mathlib の `Archimedean.embedReal`)。 -/
theorem scale_exists_of_archimedean {L : Type*} [AddCommGroup L] [LinearOrder L]
    [IsOrderedAddMonoid L] [Archimedean L] (u : L) (hu : 0 < u) :
    ∃ f : L →+o ℝ, f u = 1 ∧ Injective f := by
  let _ : One L := ⟨u⟩
  have : ZeroLEOneClass L := ⟨hu.le⟩
  have : NeZero (1 : L) := ⟨hu.ne'⟩
  exact ⟨Archimedean.embedReal L, Archimedean.embedReal_one, Archimedean.embedReal_injective L⟩

/-- 棒の集まり `A` 上の、連結と比較の経験構造。 -/
structure ExtensiveStructure (A : Type*) where
  /-- 比較：`a` を `b` と並べたとき、`a` の他端が `b` の他端を越えない -/
  le : A → A → Prop
  /-- 連結：`a` と `b` を端と端でつなぐ -/
  cat : A → A → A
  le_total : ∀ a b, le a b ∨ le b a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- つなぎ方の組を変えても、比較では区別できない -/
  cat_assoc : ∀ a b c, le (cat (cat a b) c) (cat a (cat b c)) ∧
    le (cat a (cat b c)) (cat (cat a b) c)
  /-- つなぐ順番を入れ替えても、比較では区別できない -/
  cat_comm : ∀ a b, le (cat a b) (cat b a)
  /-- 単調性：同じ棒 `c` を継ぎ足しても比較の結果は変わらない -/
  mono : ∀ a b c, le a b ↔ le (cat a c) (cat b c)
  /-- 正値性：継ぎ足した棒は元の棒より長い -/
  pos : ∀ a b, ¬ le (cat a b) a
  /-- アルキメデス性：`a` が `b` より長ければ、`a` と `b` をそれぞれ `n + 1` 本つないだものに
  `c`, `d` を継ぎ足して比べると、十分大きな `n` で `a` の側が長くなる -/
  arch : ∀ a b c d, ¬ le a b →
    ∃ n : ℕ, le (cat ((fun x => cat x b)^[n] b) d) (cat ((fun x => cat x a)^[n] a) c)

/-- 二つの目盛りが両立する：ある `c > 0` で `mB = c * mA`。
`c` は単位の違いに対応する。同じ数学的構造を持つことと同じ量を測ることは別なので、
異なる手続きを同一視するときは、この命題を仮定か定理として明示する。 -/
def Compatible {Body : Type*} (mA mB : Body → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ b, mB b = c * mA b

namespace ExtensiveStructure

variable {A : Type*} (E : ExtensiveStructure A)

/-- `n + 1` 本の `a` をつないだ棒 -/
def copies (n : ℕ) (a : A) : A := (fun x => E.cat x a)^[n] a

/-- 目盛り `ℓ` が構造を表現する：比較を大小に、連結を和に移す。 -/
def Represents (ℓ : A → ℝ) : Prop :=
  (∀ a b, E.le a b ↔ ℓ a ≤ ℓ b) ∧ ∀ a b, ℓ (E.cat a b) = ℓ a + ℓ b

variable {E}

theorem Represents.copies {ℓ : A → ℝ} (h : E.Represents ℓ) (n : ℕ) (a : A) :
    ℓ (E.copies n a) = (n + 1) * ℓ a := by
  induction n with
  | zero => simp [ExtensiveStructure.copies]
  | succ n ih =>
    rw [ExtensiveStructure.copies, iterate_succ_apply', ← ExtensiveStructure.copies, h.2, ih]
    push_cast; ring

theorem Represents.pos {ℓ : A → ℝ} (h : E.Represents ℓ) (a : A) : 0 < ℓ a := by
  have h1 := E.pos a a
  rw [h.1, h.2] at h1
  linarith

variable (E)

/-- **一意性**：単位の棒 `u` に `1` を割り当てる表現は一つしかない。 -/
theorem length_unique (u : A) {ℓ ℓ' : A → ℝ} (h : E.Represents ℓ) (h' : E.Represents ℓ')
    (hu : ℓ u = 1) (hu' : ℓ' u = 1) : ℓ = ℓ' := by
  -- `ℓ r < ℓ' r` なら、`N` 本の `r` と `M` 本の `u` (`ℓ r < M/N < ℓ' r`) を比べて矛盾
  have key : ∀ {ℓ ℓ' : A → ℝ}, E.Represents ℓ → E.Represents ℓ' → ℓ u = 1 → ℓ' u = 1 →
      ∀ r, ¬ ℓ r < ℓ' r := by
    intro ℓ ℓ' h h' hu hu' r hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq0 : (0 : ℝ) < q := (h.pos r).trans hq1
    have hN : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hnum : (q.num : ℝ) = q * q.den := by exact_mod_cast (Rat.mul_den_eq_num q).symm
    have hnum0 : 0 < q.num := by
      have : (0 : ℝ) < q.num := by rw [hnum]; positivity
      exact_mod_cast this
    set M := q.num.toNat
    set N := q.den
    have hM : (M : ℝ) = q * N := by
      rw [← hnum]; exact_mod_cast Int.toNat_of_nonneg hnum0.le
    have hMpos : 0 < M := by omega
    have hNpos : 0 < N := q.den_pos
    have cN : ((N - 1 : ℕ) : ℝ) + 1 = N := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have cM : ((M - 1 : ℕ) : ℝ) + 1 = M := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e1 := h.copies (N - 1) r
    have e2 := h.copies (M - 1) u
    have e1' := h'.copies (N - 1) r
    have e2' := h'.copies (M - 1) u
    rw [cN] at e1 e1'
    rw [cM, hu] at e2
    rw [cM, hu'] at e2'
    rcases E.le_total (E.copies (M - 1) u) (E.copies (N - 1) r) with hle | hle
    · have := (h.1 _ _).1 hle
      rw [e1, e2, hM] at this
      nlinarith
    · have := (h'.1 _ _).1 hle
      rw [e1', e2', hM] at this
      nlinarith
  funext r
  exact le_antisymm (not_lt.1 (key h' h hu' hu r)) (not_lt.1 (key h h' hu hu' r))

/-- 同じ連結と比較の構造を表現する二つの目盛りは比例する。経験的に確かめるべきなのは、
二つの手続きが同じ構造 (同じ比較と連結の結果) を表現していることの方である。 -/
theorem compatible_of_represents {ℓA ℓB : A → ℝ} (hA : E.Represents ℓA) (hB : E.Represents ℓB)
    (u : A) : Compatible ℓA ℓB := by
  have pA := hA.pos u
  have pB := hB.pos u
  have scale : ∀ {ℓ : A → ℝ} (k : ℝ), 0 < k → E.Represents ℓ →
      E.Represents (fun a => k * ℓ a) :=
    fun k hk h => ⟨fun a b => by rw [h.1]; exact (mul_le_mul_iff_of_pos_left hk).symm,
      fun a b => by simp only [h.2]; ring⟩
  have hu := E.length_unique u (scale _ (inv_pos.2 pA) hA) (scale _ (inv_pos.2 pB) hB)
    (inv_mul_cancel₀ pA.ne') (inv_mul_cancel₀ pB.ne')
  refine ⟨ℓB u / ℓA u, div_pos pB pA, fun b => ?_⟩
  have := congrFun hu b
  field_simp at this ⊢
  linarith

/-! ### 存在の証明：商半群 `Q` と差の群 `G` -/

/-- 比較で区別できないことによる同値関係 -/
def setoid : Setoid A where
  r a b := E.le a b ∧ E.le b a
  iseqv :=
    { refl := fun a => (E.le_total a a).elim (fun h => ⟨h, h⟩) (fun h => ⟨h, h⟩)
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h h' => ⟨E.le_trans h.1 h'.1, E.le_trans h'.2 h.2⟩ }

theorem cat_le_cat {a a' b b' : A} (ha : E.le a a') (hb : E.le b b') :
    E.le (E.cat a b) (E.cat a' b') := by
  have h1 := (E.mono a a' b).1 ha
  have h2 : E.le (E.cat a' b) (E.cat a' b') :=
    E.le_trans (E.cat_comm a' b) (E.le_trans ((E.mono b b' a').1 hb) (E.cat_comm b' a'))
  exact E.le_trans h1 h2

/-- 比較で区別できない棒を同一視した商 -/
def Q := Quotient E.setoid

namespace Q

variable {E}

/-- 棒の類 -/
def mk (a : A) : E.Q := Quotient.mk E.setoid a

instance : Add E.Q where
  add := Quotient.map₂ E.cat fun _ _ ha _ _ hb =>
    ⟨E.cat_le_cat ha.1 hb.1, E.cat_le_cat ha.2 hb.2⟩

instance : LE E.Q where
  le := Quotient.lift₂ E.le fun _ _ _ _ ha hb =>
    propext ⟨fun h => E.le_trans ha.2 (E.le_trans h hb.1),
      fun h => E.le_trans ha.1 (E.le_trans h hb.2)⟩

theorem mk_add (a b : A) : mk (E.cat a b) = (mk a + mk b : E.Q) := rfl

theorem ind {P : E.Q → Prop} (h : ∀ a, P (mk a)) (x : E.Q) : P x := Quotient.ind h x

instance : AddCommSemigroup E.Q where
  add_assoc := ind fun a => ind fun b => ind fun c => Quotient.sound (E.cat_assoc a b c)
  add_comm := ind fun a => ind fun b => Quotient.sound ⟨E.cat_comm a b, E.cat_comm b a⟩

theorem le_total (x y : E.Q) : x ≤ y ∨ y ≤ x := by
  induction x using ind; induction y using ind; exact E.le_total _ _

theorem le_refl (x : E.Q) : x ≤ x := (le_total x x).elim id id

theorem le_trans {x y z : E.Q} : x ≤ y → y ≤ z → x ≤ z := by
  induction x using ind; induction y using ind; induction z using ind; exact E.le_trans

instance : @Trans E.Q E.Q E.Q LE.le LE.le LE.le := ⟨le_trans⟩

theorem le_antisymm {x y : E.Q} : x ≤ y → y ≤ x → x = y := by
  induction x using ind; induction y using ind; exact fun h h' => Quotient.sound ⟨h, h'⟩

theorem add_le_add_iff_right (x y z : E.Q) : x + z ≤ y + z ↔ x ≤ y := by
  induction x using ind; induction y using ind; induction z using ind
  exact (E.mono _ _ _).symm

theorem add_right_cancel {x y z : E.Q} (h : x + z = y + z) : x = y :=
  le_antisymm ((add_le_add_iff_right x y z).1 (by rw [h]; exact le_refl _))
    ((add_le_add_iff_right y x z).1 (by rw [h]; exact le_refl _))

theorem not_add_le (x y : E.Q) : ¬ x + y ≤ x := by
  induction x using ind; induction y using ind; exact E.pos _ _

/-- `n + 1` 個の `x` の和 -/
def copies (n : ℕ) (x : E.Q) : E.Q := (fun y => y + x)^[n] x

theorem copies_succ (n : ℕ) (x : E.Q) : copies (n + 1) x = copies n x + x := by
  rw [copies, iterate_succ_apply', ← copies]

theorem mk_copies (n : ℕ) (a : A) : mk (E := E) (E.copies n a) = copies n (mk a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ExtensiveStructure.copies, iterate_succ_apply', ← ExtensiveStructure.copies, mk_add, ih,
      copies_succ]

theorem arch (x y z w : E.Q) (h : ¬ x ≤ y) : ∃ n, copies n y + w ≤ copies n x + z := by
  induction x using ind; induction y using ind; induction z using ind; induction w using ind
  obtain ⟨n, hn⟩ := E.arch _ _ _ _ h
  refine ⟨n, ?_⟩
  rw [← mk_copies, ← mk_copies, ← mk_add, ← mk_add]
  exact hn

end Q

/-- 形式的な差 `(x, y) ↦ x - y` の同値関係 -/
def diffSetoid : Setoid (E.Q × E.Q) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv :=
    { refl := fun _ => rfl
      symm := fun h => h.symm
      trans := by
        intro p q r h h'
        apply Q.add_right_cancel (z := q.2)
        calc p.1 + r.2 + q.2 = (p.1 + q.2) + r.2 := by ac_rfl
          _ = (q.1 + p.2) + r.2 := by rw [h]
          _ = (q.1 + r.2) + p.2 := by ac_rfl
          _ = (r.1 + q.2) + p.2 := by rw [h']
          _ = r.1 + p.2 + q.2 := by ac_rfl }

/-- 差の群 -/
def G := Quotient E.diffSetoid

namespace G

variable {E}

/-- 形式的な差 `x - y` -/
def mk (x y : E.Q) : E.G := Quotient.mk E.diffSetoid (x, y)

theorem ind {P : E.G → Prop} (h : ∀ x y, P (mk x y)) (z : E.G) : P z :=
  Quotient.ind (fun p => h p.1 p.2) z

theorem mk_eq {x y z w : E.Q} : mk x y = mk z w ↔ x + w = z + y := Quotient.eq

variable [Nonempty A]

/-- 基準に使う任意の類 -/
noncomputable def q₀ : E.Q := Q.mk (Classical.arbitrary A)

noncomputable instance : Zero E.G := ⟨mk q₀ q₀⟩

instance : Add E.G where
  add := Quotient.map₂ (fun p q => (p.1 + q.1, p.2 + q.2)) fun p p' h q q' h' => by
    change (p.1 + q.1) + (p'.2 + q'.2) = (p'.1 + q'.1) + (p.2 + q.2)
    calc (p.1 + q.1) + (p'.2 + q'.2) = (p.1 + p'.2) + (q.1 + q'.2) := by ac_rfl
      _ = (p'.1 + p.2) + (q'.1 + q.2) := by rw [show p.1 + p'.2 = p'.1 + p.2 from h,
            show q.1 + q'.2 = q'.1 + q.2 from h']
      _ = (p'.1 + q'.1) + (p.2 + q.2) := by ac_rfl

instance : Neg E.G where
  neg := Quotient.map Prod.swap fun p p' h => by
    change p.2 + p'.1 = p'.2 + p.1
    rw [add_comm, ← show p.1 + p'.2 = p'.1 + p.2 from h, add_comm]

omit [Nonempty A] in
theorem mk_add (x y z w : E.Q) : mk x y + mk z w = mk (x + z) (y + w) := rfl

omit [Nonempty A] in
theorem neg_mk (x y : E.Q) : -mk x y = mk y x := rfl

theorem zero_def : (0 : E.G) = mk q₀ q₀ := rfl

noncomputable instance : AddCommGroup E.G where
  add_assoc := ind fun a b => ind fun c d => ind fun e f => by
    simp only [mk_add, add_assoc]
  zero_add := ind fun a b => by
    rw [zero_def, mk_add, mk_eq]; ac_rfl
  add_zero := ind fun a b => by
    rw [zero_def, mk_add, mk_eq]; ac_rfl
  neg_add_cancel := ind fun a b => by
    rw [neg_mk, mk_add, zero_def, mk_eq]; ac_rfl
  add_comm := ind fun a b => ind fun c d => by
    rw [mk_add, mk_add, mk_eq]; ac_rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : LE E.G where
  le := Quotient.lift₂ (fun p q => p.1 + q.2 ≤ q.1 + p.2) fun p q p' q' hp hq => by
    have hp : p.1 + p'.2 = p'.1 + p.2 := hp
    have hq : q.1 + q'.2 = q'.1 + q.2 := hq
    apply propext
    rw [← Q.add_le_add_iff_right (p.1 + q.2) (q.1 + p.2) (p'.2 + q'.2),
      ← Q.add_le_add_iff_right (p'.1 + q'.2) (q'.1 + p'.2) (p.2 + q.2)]
    have e1 : (p.1 + q.2) + (p'.2 + q'.2) = (p'.1 + q'.2) + (p.2 + q.2) :=
      calc (p.1 + q.2) + (p'.2 + q'.2) = (p.1 + p'.2) + (q.2 + q'.2) := by ac_rfl
        _ = (p'.1 + p.2) + (q.2 + q'.2) := by rw [hp]
        _ = (p'.1 + q'.2) + (p.2 + q.2) := by ac_rfl
    have e2 : (q.1 + p.2) + (p'.2 + q'.2) = (q'.1 + p'.2) + (p.2 + q.2) :=
      calc (q.1 + p.2) + (p'.2 + q'.2) = (q.1 + q'.2) + (p.2 + p'.2) := by ac_rfl
        _ = (q'.1 + q.2) + (p.2 + p'.2) := by rw [hq]
        _ = (q'.1 + p'.2) + (p.2 + q.2) := by ac_rfl
    rw [e1, e2]

omit [Nonempty A] in
theorem mk_le_mk (x y z w : E.Q) : mk x y ≤ mk z w ↔ x + w ≤ z + y := Iff.rfl

noncomputable instance : LinearOrder E.G where
  le_refl := ind fun a b => Q.le_refl _
  le_trans := ind fun a b => ind fun c d => ind fun e f => by
    simp only [mk_le_mk]
    intro h1 h2
    rw [← Q.add_le_add_iff_right (a + f) (e + b) d]
    calc a + f + d = (a + d) + f := by ac_rfl
      _ ≤ (c + b) + f := (Q.add_le_add_iff_right _ _ f).2 h1
      _ = (c + f) + b := by ac_rfl
      _ ≤ (e + d) + b := (Q.add_le_add_iff_right _ _ b).2 h2
      _ = e + b + d := by ac_rfl
  le_antisymm := ind fun a b => ind fun c d => fun h1 h2 =>
    mk_eq.2 (Q.le_antisymm h1 h2)
  le_total := ind fun a b => ind fun c d => Q.le_total _ _
  toDecidableLE := Classical.decRel _

instance : IsOrderedAddMonoid E.G where
  add_le_add_left := ind fun a b => ind fun c d => fun h => ind fun e f => by
    rw [mk_add, mk_add, mk_le_mk]
    rw [mk_le_mk] at h
    calc a + e + (d + f) = (a + d) + (e + f) := by ac_rfl
      _ ≤ (c + b) + (e + f) := (Q.add_le_add_iff_right _ _ _).2 h
      _ = c + e + (b + f) := by ac_rfl

theorem succ_nsmul_mk (n : ℕ) (x y : E.Q) :
    (n + 1) • mk x y = mk (Q.copies n x) (Q.copies n y) := by
  induction n with
  | zero => rw [zero_add, one_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih, mk_add, ← Q.copies_succ, ← Q.copies_succ]

theorem not_le_zero_iff (x y : E.Q) : ¬ mk x y ≤ 0 ↔ ¬ x ≤ y := by
  rw [zero_def, mk_le_mk, add_comm q₀ y, Q.add_le_add_iff_right]

instance : Archimedean E.G where
  arch := ind fun a b => by
    intro z
    induction z using ind with
    | h c d =>
      intro hpos
      have hcd : ¬ c ≤ d := (not_le_zero_iff c d).1 (not_le.2 hpos)
      obtain ⟨n, hn⟩ := Q.arch c d b a hcd
      refine ⟨n + 1, ?_⟩
      rw [succ_nsmul_mk, mk_le_mk, add_comm a]
      exact hn

/-- 棒の類 `x` を群の元 `(x + x) - x` として見る -/
def ι (x : E.Q) : E.G := mk (x + x) x

omit [Nonempty A] in
theorem ι_add (x y : E.Q) : ι (x + y) = ι x + ι y := by
  rw [ι, ι, ι, mk_add, mk_eq]; ac_rfl

omit [Nonempty A] in
theorem ι_le_iff (x y : E.Q) : ι x ≤ ι y ↔ x ≤ y := by
  rw [ι, ι, mk_le_mk, show x + x + y = x + (x + y) by ac_rfl,
    show y + y + x = y + (x + y) by ac_rfl, Q.add_le_add_iff_right]

theorem ι_pos (x : E.Q) : 0 < ι x := by
  apply not_le.1
  rw [ι, not_le_zero_iff]
  exact Q.not_add_le x x

end G

/-- **存在** (Hölder)：単位の棒 `u` を選ぶと、構造を表現する目盛りで `ℓ u = 1` を満たすものが
存在する。`Represents.pos` により値はすべて正である。 -/
theorem length_exists (u : A) : ∃ ℓ : A → ℝ, E.Represents ℓ ∧ ℓ u = 1 := by
  have : Nonempty A := ⟨u⟩
  obtain ⟨f, hf1, hfinj⟩ := scale_exists_of_archimedean (G.ι (Q.mk (E := E) u)) (G.ι_pos _)
  have hmono : StrictMono f := (OrderHomClass.mono f).strictMono_of_injective hfinj
  refine ⟨fun a => f (G.ι (Q.mk a)), ⟨fun a b => ?_, fun a b => ?_⟩, hf1⟩
  · rw [hmono.le_iff_le, G.ι_le_iff]; rfl
  · change f (G.ι (Q.mk (E.cat a b))) = f (G.ι (Q.mk a)) + f (G.ι (Q.mk b))
    rw [Q.mk_add, G.ι_add, map_add]

end ExtensiveStructure

end OpThermo
