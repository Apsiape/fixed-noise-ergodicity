/-
# §9.1: lists read by one moving token

`W` is a plane-safe set of token states for `R_M` (`set:def-safe`).
* **`thr:move`** (`thr_move`): if `s'` is compatible with `s` at `d ∈ D`, then `ctr(s') = λ(d)`
  for the block `λ` of `s`, and the class `quad(ctr ·) − site (mod 2)` does not change
  (`cls_block`: the class is constant on a legal block, by (Q1) along paths inside `Λ`). The axis
  cases as matchings of the centres: `ctr_match_e1`, `ctr_match_e1'`, `ctr_match_e2`,
  `ctr_match_e2'`.
* A token walks to any site through moves (`walk_token`, from (W3)).
* **`thr:phase`** (`thr_phase`, `classPart_safe`, `exists_classPart`).
* **`thr:def-pins`**: pin pairs (`PinPair`, `IsPinPair`), walker sets (`walker`), `ι` (`iota`),
  index lists (`indexLists`), for `3`-token states.
* **`thr:lists`** (a) `walker_total`, `walker_move`; (b) `walker_pin1`, `walker_pin2`;
  (c) `lists_family`, `lists_ac` (an `IsListFamily` that is `ArcConsistent`, so the lemmas of
  `Three/Lists.lean`, `Coarse.lean`, `Dyadic.lean`, `Pairs.lean` apply); (d) `lists_pin1`,
  `lists_pin2`.

**[choice]** A pin pair is a structure `(p₁, s₁, p₂, s₂)`; a `3`-token state is
`(![p₁, p₂, x], ![s₁, s₂, s])` (`pinState`; token `3` of the paper is index `2`). The class of
`thr:phase` is the pair `cls` of `Three/Interface.lean`, and `ι(z) = γ + 2z` is written with
explicit coordinates (`iota`). `thr:lists`(c),(d) assume that every state of `W` has class `γ`
(`hγ`), which holds for the component `𝒲_γ` (`classPart`).
-/
import FixedNoiseErgodicity.Three.Interface
import FixedNoiseErgodicity.Three.Pairs
import FixedNoiseErgodicity.Section2.TokenGame

set_option autoImplicit false

namespace FNE.Three

open FNE FNE.Scaffold FNE.Family FNE.TokenGame

/-! ## `thr:move` -/

theorem mem_box1_of_moore {d : Plane} (hd : d ∈ mooreDirs) : d ∈ box 1 :=
  Finset.mem_of_mem_erase hd

/-- The centre of a live symbol is a tile of the Wang set. -/
theorem ctr_mem {R : WangSet} (s : LiveSymbol R) : ctr s ∈ R := (s.1.1 Cell.zero).2

/-- **`thr:move`**, first claim: if `s'` is compatible with `s` at displacement `d ∈ Λ`, then
`ctr(s') = λ(d)` for the block `λ` of `s`. -/
theorem ctr_of_compatible {R : WangSet} {s s' : LiveSymbol R} {d : Plane} (hd : d ∈ box 1)
    (h : Compatible s s' d) : ctr s' = (s.1.1 ⟨d, hd⟩).1 := by
  have := h.2 ⟨d, hd⟩ Cell.zero (by show ((0, 0) : Plane) = d - d; rw [sub_self]; rfl)
  unfold ctr
  rw [← this]

section Match

variable {R : WangSet} {s s' : LiveSymbol R}

/-- `thr:move` at `d = e₁`: `ctr(s)` and `ctr(s')` match horizontally. -/
theorem ctr_match_e1 (h : Compatible s s' (1, 0)) : (ctr s).E = (ctr s').W := by
  rw [ctr_of_compatible (by decide) h]
  exact s.1.2.1 Cell.zero ⟨(1, 0), by decide⟩ (by decide)

/-- `thr:move` at `d = -e₁`: `ctr(s')` and `ctr(s)` match horizontally. -/
theorem ctr_match_e1' (h : Compatible s s' (-1, 0)) : (ctr s').E = (ctr s).W := by
  rw [ctr_of_compatible (by decide) h]
  exact s.1.2.1 ⟨(-1, 0), by decide⟩ Cell.zero (by decide)

/-- `thr:move` at `d = e₂`: `ctr(s)` and `ctr(s')` match vertically. -/
theorem ctr_match_e2 (h : Compatible s s' (0, 1)) : (ctr s).N = (ctr s').S := by
  rw [ctr_of_compatible (by decide) h]
  exact s.1.2.2 Cell.zero ⟨(0, 1), by decide⟩ (by decide)

/-- `thr:move` at `d = -e₂`: `ctr(s')` and `ctr(s)` match vertically. -/
theorem ctr_match_e2' (h : Compatible s s' (0, -1)) : (ctr s').N = (ctr s).S := by
  rw [ctr_of_compatible (by decide) h]
  exact s.1.2.2 ⟨(0, -1), by decide⟩ Cell.zero (by decide)

end Match

variable {M : TuringMachine}

/-- The class `quad(λ(p)) − (u + p)` is the same at every cell `p` of the legal block `λ` of `s`
placed at `u` ((Q1) along paths of at most two steps inside `Λ`). -/
theorem cls_block (s : LiveSymbol (RM M)) (u p : Plane) (hp : p ∈ box 1) :
    cls (u + p) (s.1.1 ⟨p, hp⟩).1 = cls u (ctr s) := by
  have H : ∀ (p p' : Plane) (hp : p ∈ box 1) (hp' : p' ∈ box 1), p' = p + (1, 0) →
      cls (u + p') (s.1.1 ⟨p', hp'⟩).1 = cls (u + p) (s.1.1 ⟨p, hp⟩).1 := by
    intro p p' hp hp' e
    have hm := s.1.2.1 ⟨p, hp⟩ ⟨p', hp'⟩ e
    subst e
    rw [← add_assoc]
    exact cls_E (s.1.1 _).2 (s.1.1 _).2 hm (u + p)
  have V : ∀ (p p' : Plane) (hp : p ∈ box 1) (hp' : p' ∈ box 1), p' = p + (0, 1) →
      cls (u + p') (s.1.1 ⟨p', hp'⟩).1 = cls (u + p) (s.1.1 ⟨p, hp⟩).1 := by
    intro p p' hp hp' e
    have hm := s.1.2.2 ⟨p, hp⟩ ⟨p', hp'⟩ e
    subst e
    rw [← add_assoc]
    exact cls_N (s.1.1 _).2 (s.1.1 _).2 hm (u + p)
  have h0 : cls (u + (0, 0)) (s.1.1 ⟨(0, 0), by decide⟩).1 = cls u (ctr s) := by
    show cls (u + 0) (s.1.1 Cell.zero).1 = cls u (ctr s)
    rw [add_zero]; rfl
  obtain ⟨a, b⟩ := p
  have hab := mem_box_iff.1 hp
  simp only [Nat.cast_one] at hab
  have ha : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  have hb : b = -1 ∨ b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rw [← H (-1, -1) (0, -1) hp (by decide) (by decide),
      ← V (0, -1) (0, 0) (by decide) (by decide) (by decide), h0]
  · rw [← H (-1, 0) (0, 0) hp (by decide) (by decide), h0]
  · rw [← H (-1, 1) (0, 1) hp (by decide) (by decide),
      V (0, 0) (0, 1) (by decide) (by decide) (by decide), h0]
  · rw [← V (0, -1) (0, 0) hp (by decide) (by decide), h0]
  · exact h0
  · rw [V (0, 0) (0, 1) (by decide) hp (by decide), h0]
  · rw [H (0, -1) (1, -1) (by decide) hp (by decide),
      ← V (0, -1) (0, 0) (by decide) (by decide) (by decide), h0]
  · rw [H (0, 0) (1, 0) (by decide) hp (by decide), h0]
  · rw [V (1, 0) (1, 1) (by decide) hp (by decide),
      H (0, 0) (1, 0) (by decide) (by decide) (by decide), h0]

/-- **`thr:move`.** Let `s'` be compatible with `s` at `d ∈ D`, and `λ` the block of `s`. Then
`ctr(s') = λ(d)`, and `quad(ctr(s')) − (u + d) ≡ quad(ctr(s)) − u (mod 2)` for every `u`. -/
theorem thr_move {s s' : LiveSymbol (RM M)} {d : Plane} (hd : d ∈ mooreDirs)
    (h : Compatible s s' d) (u : Plane) :
    ctr s' = (s.1.1 ⟨d, mem_box1_of_moore hd⟩).1 ∧ cls (u + d) (ctr s') = cls u (ctr s) := by
  have e := ctr_of_compatible (mem_box1_of_moore hd) h
  exact ⟨e, by rw [e]; exact cls_block s u d _⟩

/-! ## Walking one token -/

section Walk

variable {R : WangSet} {j : ℕ} {W : Set (State R j)}

theorem vec_mem_moore (d : Dir) : d.vec ∈ mooreDirs := by cases d <;> decide

theorem neg_vec_mem_moore (d : Dir) : -d.vec ∈ mooreDirs := by cases d <;> decide

/-- A token walks to any site `x` through moves (W3), the other tokens staying in place; a
property of (site, symbol) that moves preserve holds at the end. -/
theorem walk_token (hW : IsPlaneSafe W) (P : Plane → LiveSymbol R → Prop)
    (hP : ∀ u s s' d, d ∈ mooreDirs → Compatible s s' d → P u s → P (u + d) s')
    {st : State R j} (hst : st ∈ W) (i : Fin j) (hi : P (st.1 i) (st.2 i)) (x : Plane) :
    ∃ s', P x s' ∧ (Function.update st.1 i x, Function.update st.2 i s') ∈ W := by
  refine plane_induction (P := fun y => ∃ s', P y s' ∧
    (Function.update st.1 i y, Function.update st.2 i s') ∈ W) (st.1 i)
    ⟨st.2 i, hi, by simpa using hst⟩ ?_ x
  rintro z d ⟨s', hs', hmem⟩
  obtain ⟨s'', hc, hm⟩ := hW.move_mem _ hmem i (-d.vec) (neg_vec_mem_moore d) (Set.mem_univ _)
  have hz : z + d.vec + -d.vec = z := add_neg_cancel_right z d.vec
  simp only [Function.update_self] at hc
  refine ⟨s'', ?_, ?_⟩
  · have := hP _ _ _ _ (neg_vec_mem_moore d) hc hs'
    rwa [hz] at this
  · simpa [move, Function.update_idem, hz] using hm

end Walk

/-! ## `thr:phase` -/

section Phase

variable {j : ℕ} {W : Set (State (RM M) j)}

/-- **`thr:phase`**, first claim: in every state of a plane-safe set, the classes
`quad(ctr(s_i)) − u_i (mod 2)` of all tokens are equal. -/
theorem thr_phase (hW : IsPlaneSafe W) {st : State (RM M) j} (hst : st ∈ W) (i i' : Fin j) :
    cls (st.1 i) (ctr (st.2 i)) = cls (st.1 i') (ctr (st.2 i')) := by
  by_cases hii : i = i'
  · subst hii; rfl
  obtain ⟨s'', hP, hmem⟩ := walk_token hW
    (fun y s => cls y (ctr s) = cls (st.1 i) (ctr (st.2 i)))
    (fun u s s' d hd hc hu => by rw [(thr_move hd hc u).2, hu]) hst i rfl
    (st.1 i')
  have hco := hW.coinc _ hmem i i' (by simp [Ne.symm hii])
  simp only [Function.update_self, Function.update_of_ne (Ne.symm hii)] at hco
  rw [← hP, hco]

/-- `thr:phase`: the phase-`γ` component `𝒲_γ`, the states whose common class is `γ`. -/
def classPart (W : Set (State (RM M) j)) (γ : Plane) : Set (State (RM M) j) :=
  {st | st ∈ W ∧ ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ}

/-- **`thr:phase`**: each `𝒲_γ` is plane-safe. -/
theorem classPart_safe (hW : IsPlaneSafe W) (γ : Plane) : IsPlaneSafe (classPart W γ) where
  pos _ _ _ := Set.mem_univ _
  coinc st hst := hW.coinc st hst.1
  clone_mem st hst i i' hii' := by
    refine ⟨hW.clone_mem st hst.1 i i' hii', fun l => ?_⟩
    simp only [clone, Function.update_apply]
    split_ifs
    · exact hst.2 i
    · exact hst.2 l
  move_mem st hst i d hd _ := by
    obtain ⟨s', hc, hm⟩ := hW.move_mem st hst.1 i d hd (Set.mem_univ _)
    refine ⟨s', hc, hm, fun l => ?_⟩
    simp only [move, Function.update_apply]
    split_ifs with h
    · rw [(thr_move hd hc (st.1 i)).2]; exact hst.2 i
    · exact hst.2 l

/-- **`thr:phase`**: every state of `𝒲` lies in the component of its class; in particular some
`𝒲_γ` is nonempty if `𝒲` is. -/
theorem exists_classPart (hW : IsPlaneSafe W) (hne : W.Nonempty) (i₀ : Fin j) :
    ∃ γ, (classPart W γ).Nonempty := by
  obtain ⟨st, hst⟩ := hne
  exact ⟨cls (st.1 i₀) (ctr (st.2 i₀)), st, hst, fun i => thr_phase hW hst i i₀⟩

end Phase

/-! ## Pins, walker sets and index lists (`thr:def-pins`) -/

/-- `thr:def-pins`: a pin pair `𝐩 = (p₁, s₁; p₂, s₂)`. -/
structure PinPair (R : WangSet) where
  /-- the site of token `1` -/
  p1 : Plane
  /-- the symbol of token `1` -/
  s1 : LiveSymbol R
  /-- the site of token `2` -/
  p2 : Plane
  /-- the symbol of token `2` -/
  s2 : LiveSymbol R

/-- The `3`-token state `((p₁, p₂, x), (s₁, s₂, s))`. -/
def pinState {R : WangSet} (P : PinPair R) (x : Plane) (s : LiveSymbol R) : State R 3 :=
  (![P.p1, P.p2, x], ![P.s1, P.s2, s])

/-- `thr:def-pins`: the walker set `𝒳_𝐩 = {(x, s) : ((p₁, p₂, x), (s₁, s₂, s)) ∈ 𝒲}`. -/
def walker {R : WangSet} (W : Set (State R 3)) (P : PinPair R) : Set (Plane × LiveSymbol R) :=
  {xs | pinState P xs.1 xs.2 ∈ W}

/-- `thr:def-pins`: `𝐩` is a pin pair (of `𝒲`): some state `((p₁, p₂, x), (s₁, s₂, s))` lies in
`𝒲`. -/
def IsPinPair {R : WangSet} (W : Set (State R 3)) (P : PinPair R) : Prop := (walker W P).Nonempty

/-- `ι(z) = γ + 2z` (07:65). -/
def iota (γ z : Plane) : Plane := (γ.1 + 2 * z.1, γ.2 + 2 * z.2)

/-- `thr:def-pins`: the index lists `𝓛_𝐩(z) = {par(ctr(s)) : (ι(z), s) ∈ 𝒳_𝐩}`. -/
def indexLists (W : Set (State (RM M) 3)) (γ : Plane) (P : PinPair (RM M)) (z : Plane) :
    Set Letter :=
  {a | ∃ s, (iota γ z, s) ∈ walker W P ∧ tpar (ctr s) = a}

theorem vec3_eq {α : Type*} {f : Fin 3 → α} {a b c : α} (h0 : f 0 = a) (h1 : f 1 = b)
    (h2 : f 2 = c) : f = ![a, b, c] := by
  funext i; fin_cases i <;> assumption

theorem update_vec3_two {α : Type*} (a b c c' : α) : Function.update ![a, b, c] 2 c' = ![a, b, c'] :=
  vec3_eq rfl rfl rfl

theorem iota_add (γ z : Plane) (d : Dir) : iota γ (z + d.vec) = iota γ z + d.vec + d.vec := by
  cases d <;> ext <;> simp [iota, Dir.vec] <;> ring

/-! ## `thr:lists` -/

section Lists

variable {R : WangSet} {W : Set (State R 3)} {P : PinPair R}

/-- **`thr:lists`(a)**, second claim: the walker moves (W3 for token `3`). -/
theorem walker_move (hW : IsPlaneSafe W) {x : Plane} {s : LiveSymbol R} (h : (x, s) ∈ walker W P)
    {d : Plane} (hd : d ∈ mooreDirs) : ∃ s', Compatible s s' d ∧ (x + d, s') ∈ walker W P := by
  obtain ⟨s', hc, hm⟩ := hW.move_mem _ h 2 d hd (Set.mem_univ _)
  refine ⟨s', hc, ?_⟩
  show pinState P (x + d) s' ∈ W
  convert hm using 1
  simp only [move, pinState]
  rw [update_vec3_two, update_vec3_two]
  rfl

/-- **`thr:lists`(a)**, first claim: for every `x` some `s` has `(x, s) ∈ 𝒳_𝐩`. -/
theorem walker_total (hW : IsPlaneSafe W) (hP : IsPinPair W P) (x : Plane) :
    ∃ s, (x, s) ∈ walker W P := by
  obtain ⟨⟨x0, s0⟩, h0⟩ := hP
  obtain ⟨s', -, hm⟩ := walk_token hW (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) h0 2
    trivial x
  refine ⟨s', ?_⟩
  show pinState P x s' ∈ W
  simpa only [pinState, update_vec3_two] using hm

/-- **`thr:lists`(b)** for the first pin. -/
theorem walker_pin1 (hW : IsPlaneSafe W) {s : LiveSymbol R} (h : (P.p1, s) ∈ walker W P) :
    s = P.s1 :=
  hW.coinc _ h 2 0 rfl

/-- **`thr:lists`(b)** for the second pin. -/
theorem walker_pin2 (hW : IsPlaneSafe W) {s : LiveSymbol R} (h : (P.p2, s) ∈ walker W P) :
    s = P.s2 :=
  hW.coinc _ h 2 1 rfl

/-- Cloning token `3` onto token `2` makes `(p₁, s₁; x, s)` a pin pair. -/
theorem pin_clone_two (hW : IsPlaneSafe W) {x : Plane} {s : LiveSymbol R}
    (h : (x, s) ∈ walker W P) : IsPinPair W ⟨P.p1, P.s1, x, s⟩ := by
  refine ⟨(x, s), ?_⟩
  have := hW.clone_mem _ h 2 1 (by decide)
  show pinState _ x s ∈ W
  convert this using 1
  simp only [pinState, clone]
  ext i <;> fin_cases i <;> rfl

/-- Cloning token `3` onto token `1` makes `(x, s; p₂, s₂)` a pin pair. -/
theorem pin_clone_one (hW : IsPlaneSafe W) {x : Plane} {s : LiveSymbol R}
    (h : (x, s) ∈ walker W P) : IsPinPair W ⟨x, s, P.p2, P.s2⟩ := by
  refine ⟨(x, s), ?_⟩
  have := hW.clone_mem _ h 2 0 (by decide)
  show pinState _ x s ∈ W
  convert this using 1
  simp only [pinState, clone]
  ext i <;> fin_cases i <;> rfl

/-- Cloning token `3` onto tokens `1` and `2` makes `(x, s; x, s)` a pin pair (a single pin held
by two tokens). -/
theorem pin_clone_both (hW : IsPlaneSafe W) {x : Plane} {s : LiveSymbol R}
    (h : (x, s) ∈ walker W P) : IsPinPair W ⟨x, s, x, s⟩ := by
  refine ⟨(x, s), ?_⟩
  have := cloneAll_mem hW h 2
  show pinState _ x s ∈ W
  convert this using 1
  simp only [pinState]
  ext i <;> fin_cases i <;> rfl

end Lists

section ListsRM

variable {W : Set (State (RM M) 3)} {γ : Plane} {P : PinPair (RM M)}

/-- At the site `ι(z)` the walker's centre has quadrant `(0, 0)`, if every state of `𝒲` has
class `γ`. -/
theorem quad_iota (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ) {z : Plane}
    {s : LiveSymbol (RM M)} (h : (iota γ z, s) ∈ walker W P) : tquad (ctr s) = (false, false) := by
  have hc : cls (iota γ z) (ctr s) = γ := hγ _ h 2
  obtain ⟨h1, h2⟩ := quad_of_cls hc
  simp only [iota] at h1 h2
  have e1 : bitZ (tquad (ctr s)).1 = 0 := by rw [h1]; omega
  have e2 : bitZ (tquad (ctr s)).2 = 0 := by rw [h2]; omega
  exact Prod.ext (eq_false_of_bitZ e1) (eq_false_of_bitZ e2)

variable {t t' t'' : Tile}

/-- Two steps east from a quarter with first coordinate `0`: the first step stays in the parent
cell, the second crosses to the next parent, which matches horizontally ((Q1) twice). -/
theorem two_steps_E (ht : t ∈ RM M) (ht' : t' ∈ RM M) (ht'' : t'' ∈ RM M) (m1 : t.E = t'.W)
    (m2 : t'.E = t''.W) (hq : (tquad t).1 = false) : Letter.MatchE (tpar t) (tpar t'') := by
  obtain ⟨q1, -, h1⟩ := Q1_E ht ht' m1
  obtain ⟨-, -, h2⟩ := Q1_E ht' ht'' m2
  rw [hq] at q1 h1
  simp only [Bool.not_false, Bool.false_eq_true, false_and, or_false, true_and] at q1 h1
  rw [q1] at h2
  simp only [Bool.true_eq_false, false_and, true_and, false_or] at h2
  rwa [h1] at h2

/-- Two steps west from a quarter with first coordinate `0`. -/
theorem two_steps_W (ht : t ∈ RM M) (ht' : t' ∈ RM M) (ht'' : t'' ∈ RM M) (m1 : t'.E = t.W)
    (m2 : t''.E = t'.W) (hq : (tquad t).1 = false) : Letter.MatchE (tpar t'') (tpar t) := by
  obtain ⟨q1, -, h1⟩ := Q1_E ht' ht m1
  obtain ⟨q2, -, h2⟩ := Q1_E ht'' ht' m2
  rw [hq] at q1
  have hq' : (tquad t').1 = true := by simpa using q1.symm
  rw [hq'] at h1 q2
  simp only [Bool.true_eq_false, false_and, true_and, false_or] at h1
  have hq'' : (tquad t'').1 = false := by simpa using q2.symm
  rw [hq''] at h2
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h2
  rwa [← h2]

/-- Two steps north from a quarter with second coordinate `0`. -/
theorem two_steps_N (ht : t ∈ RM M) (ht' : t' ∈ RM M) (ht'' : t'' ∈ RM M) (m1 : t.N = t'.S)
    (m2 : t'.N = t''.S) (hq : (tquad t).2 = false) : Letter.MatchN (tpar t) (tpar t'') := by
  obtain ⟨q1, -, h1⟩ := Q1_N ht ht' m1
  obtain ⟨-, -, h2⟩ := Q1_N ht' ht'' m2
  rw [hq] at q1 h1
  simp only [Bool.not_false, Bool.false_eq_true, false_and, or_false, true_and] at q1 h1
  rw [q1] at h2
  simp only [Bool.true_eq_false, false_and, true_and, false_or] at h2
  rwa [h1] at h2

/-- Two steps south from a quarter with second coordinate `0`. -/
theorem two_steps_S (ht : t ∈ RM M) (ht' : t' ∈ RM M) (ht'' : t'' ∈ RM M) (m1 : t'.N = t.S)
    (m2 : t''.N = t'.S) (hq : (tquad t).2 = false) : Letter.MatchN (tpar t'') (tpar t) := by
  obtain ⟨q1, -, h1⟩ := Q1_N ht' ht m1
  obtain ⟨q2, -, h2⟩ := Q1_N ht'' ht' m2
  rw [hq] at q1
  have hq' : (tquad t').2 = true := by simpa using q1.symm
  rw [hq'] at h1 q2
  simp only [Bool.true_eq_false, false_and, true_and, false_or] at h1
  have hq'' : (tquad t'').2 = false := by simpa using q2.symm
  rw [hq''] at h2
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h2
  rwa [← h2]

/-- **`thr:lists`(c)**, first part: `𝓛_𝐩` is a list family (nonempty lists by (a); parents are
letters of `𝔸`). -/
theorem lists_family (hW : IsPlaneSafe W) (hP : IsPinPair W P) :
    IsListFamily (indexLists W γ P) where
  nonempty z := by
    obtain ⟨s, hs⟩ := walker_total hW hP (iota γ z)
    exact ⟨_, s, hs, rfl⟩
  inA z := by
    rintro _ ⟨s, -, rfl⟩
    exact tpar_inA (ctr_mem s)

/-- **`thr:lists`(c)**: `𝓛_𝐩` is arc consistent. -/
theorem lists_ac (hW : IsPlaneSafe W) (hγ : ∀ st ∈ W, ∀ i, cls (st.1 i) (ctr (st.2 i)) = γ) :
    ArcConsistent (indexLists W γ P) := by
  rintro z _ ⟨s, hs, rfl⟩ d
  have hq := quad_iota hγ hs
  obtain ⟨s', hc', hs'⟩ := walker_move hW hs (vec_mem_moore d)
  obtain ⟨s'', hc'', hs''⟩ := walker_move hW hs' (vec_mem_moore d)
  refine ⟨tpar (ctr s''), ⟨s'', by rw [iota_add]; exact hs'', rfl⟩, ?_⟩
  have h0 := ctr_mem s
  have h1 := ctr_mem s'
  have h2 := ctr_mem s''
  cases d
  · exact fits_e1.2 (two_steps_E h0 h1 h2 (ctr_match_e1 hc') (ctr_match_e1 hc'')
      (by rw [hq]))
  · exact fits_e1'.2 (two_steps_W h0 h1 h2 (ctr_match_e1' hc') (ctr_match_e1' hc'')
      (by rw [hq]))
  · exact fits_e2.2 (two_steps_N h0 h1 h2 (ctr_match_e2 hc') (ctr_match_e2 hc'')
      (by rw [hq]))
  · exact fits_e2'.2 (two_steps_S h0 h1 h2 (ctr_match_e2' hc') (ctr_match_e2' hc'')
      (by rw [hq]))

/-- **`thr:lists`(d)** for the first pin: if `p₁ = ι(y₁)`, then `𝓛_𝐩(y₁) = {par(ctr(s₁))}`. -/
theorem lists_pin1 (hW : IsPlaneSafe W) (hP : IsPinPair W P) {y : Plane} (hy : P.p1 = iota γ y) :
    indexLists W γ P y = {tpar (ctr P.s1)} := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [← hy] at hs
    rw [walker_pin1 hW hs]; rfl
  · rintro rfl
    obtain ⟨s, hs⟩ := walker_total hW hP (iota γ y)
    refine ⟨s, hs, ?_⟩
    rw [← hy] at hs
    rw [walker_pin1 hW hs]

/-- **`thr:lists`(d)** for the second pin. -/
theorem lists_pin2 (hW : IsPlaneSafe W) (hP : IsPinPair W P) {y : Plane} (hy : P.p2 = iota γ y) :
    indexLists W γ P y = {tpar (ctr P.s2)} := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [← hy] at hs
    rw [walker_pin2 hW hs]; rfl
  · rintro rfl
    obtain ⟨s, hs⟩ := walker_total hW hP (iota γ y)
    refine ⟨s, hs, ?_⟩
    rw [← hy] at hs
    rw [walker_pin2 hW hs]

end ListsRM

end FNE.Three
