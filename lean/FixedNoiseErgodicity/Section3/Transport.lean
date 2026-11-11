/-
# Section 3 (forgetting): the deterministic chain

Printed Section 3 ("Bounded-width refutations give forgetting", source file `04-forgetting.tex`),
Sections 3.1–3.3. Proved here, for every initial configuration and every realisation of the noise:
* `fgt:stable`(b): families of pairs closed under coincidence and cloning lie in `Inst(S)`;
* `fgt:transport`: a clean present pair that violates `S^w_{n+1}` has violating parents on one
  common set `Γ` in at least `k + 1 - j` provider planes;
* `fgt:cover`: for `k ≥ 2j`, every present pair that violates `S^w_n` (with `n ≤ t`) contains a
  marked point of the domination field;
* `fgt:live`: after the refutation time every live site is marked.

**[choice]** Relative positions. The paper writes a pair as `(𝐳, 𝐛)` with `𝐳 ∈ (w + V)^j` and
compares it with the translated table `S^w_n(𝐳) = S_n(𝐳 - w)`. We store the pair as the token
state `(𝐳 - w, 𝐛)`; then `𝐳 ∈ (w + V)^j` reads "every position lies in `box r`", and
"`(𝐳, 𝐛)` violates `S^w_n`" reads `(𝐳 - w, 𝐛) ∉ tables R j r n`. The sets `Γ` and the map `π`
of `fgt:transport` are likewise stated in relative positions (subtract `w`).
Times: a pair present at time `t + 1` is clean when no `((w + z_l, P), t + 1)` is an event, i.e.
`ω (t, ·)` has flag `false` there (noise index `t` is time `t + 1`).
-/
import FixedNoiseErgodicity.Section4.Deterministic
import FixedNoiseErgodicity.Section2.TokenGame

set_option autoImplicit false

namespace FNE

open TokenGame

variable {k : ℕ} {R : WangSet} {j : ℕ}

/-! ## Present and clean pairs (`fgt:sec-setting`) -/

/-- `fgt:sec-setting`. The pair with relative state `st` (positions `w + st.1 l`, symbols
`st.2 l`) is *present* at plane `P` in the configuration `X`: `X(w + z_l, P) = b_l` for all `l`. -/
def PresentAt (X : Config k R) (w : Plane) (P : Fin k → ℤ) (st : State R j) : Prop :=
  ∀ l, X (w + st.1 l, P) = .live (st.2 l)

/-- `fgt:sec-setting`. The pair is *clean* at time `t + 1`: none of the points
`((w + z_l, P), t + 1)` is an event. -/
def CleanAt (ω : Noise k R) (t : ℕ) (w : Plane) (P : Fin k → ℤ) (st : State R j) : Prop :=
  ∀ l, (ω (t, (w + st.1 l, P))).1 = false

/-! ## `fgt:stable`(b) -/

/-- `fgt:stable`(b). A family `Q` of pairs in which coincident tokens carry equal symbols, which is
closed under cloning, and which lies in `S`, lies in `Inst(S)`. -/
theorem mem_inst_of_family {S Q : Set (State R j)} (h1 : ∀ st ∈ Q, Coincident st)
    (h2 : ∀ st ∈ Q, ∀ l l', l ≠ l' → clone st l l' ∈ Q) (h3 : Q ⊆ S) : Q ⊆ inst S :=
  subset_inst h3 ⟨h1, h2⟩

/-- The family of pairs present at `(w, P)` in `X` whose positions lie in `Z` (paragraph after
`fgt:stable`). -/
def presentFamily (X : Config k R) (w : Plane) (P : Fin k → ℤ) (Z : Set Plane) :
    Set (State R j) :=
  {st | (∀ l, st.1 l ∈ Z) ∧ PresentAt X w P st}

/-- Paragraph after `fgt:stable`: present families have the first two properties of
`fgt:stable`(b) (two tokens on one site read the one symbol there; clones of present pairs are
present). -/
theorem presentFamily_closed (X : Config k R) (w : Plane) (P : Fin k → ℤ) (Z : Set Plane) :
    TableClosed (presentFamily (j := j) X w P Z) where
  coinc := by
    rintro st ⟨-, hp⟩ i i' h
    have h1 := hp i
    have h2 := hp i'
    rw [h] at h1
    rw [h1] at h2
    exact Sym.live.inj h2
  clone_mem := by
    rintro st ⟨hz, hp⟩ i i' -
    refine ⟨fun l => ?_, fun l => ?_⟩
    · simp only [clone, Function.update_apply]
      split_ifs
      · exact hz i
      · exact hz l
    · simp only [clone, Function.update_apply]
      split_ifs
      · exact hp i
      · exact hp l

/-! ## Two facts about the rule -/

/-- A live output of the quorum rule meets the quorum (no hypothesis on `k` needed). -/
theorem quorumCount_of_quorumRule_eq_live {x : Config k R} {v : Site k} {s : LiveSymbol R}
    (h : quorumRule k R x v = .live s) : k ≤ quorumCount (checkAll x) v (.live s) := by
  unfold quorumRule at h
  split_ifs at h with hex
  cases h
  exact hex.choose_spec

/-- The checker outputs a live symbol only by keeping it, with all eight neighbours live and
compatible (`set:def-checker`). -/
theorem checker_live {y : Plane → Sym R} {u : Plane} {s : LiveSymbol R}
    (h : checker y u = .live s) :
    y u = .live s ∧ ∀ d ∈ mooreDirs, ∃ s', y (u + d) = .live s' ∧ Compatible s s' d := by
  unfold checker at h
  split_ifs at h with hk
  obtain ⟨s₀, hs₀, hall⟩ := hk
  rw [hs₀] at h
  cases h
  exact ⟨hs₀, hall⟩

/-! ## `fgt:transport` -/

/-- **`fgt:transport`.** Fix `x`, a noise realisation and the run `X` from `x`. Let the pair with
relative state `st` (positions in `V = box r`) be present at `(P, t + 1)`, clean, and violate
`S^w_{n+1}`. Then there are a set `Γ ⊆ V` with `|Γ| ≤ j`, a map `π` with `z - π(z) ∈ {-1,0,1}²`
and `π(z)` a position of `st` for every `z ∈ Γ`, and a set `I` of at least `k + 1 - j` providers,
such that for every `i ∈ I` some pair with positions in `Γ` is present at `(P + c_i, t)` and
violates `S^w_n`. (`Γ` and `π` are chosen before `i`.) -/
theorem transport {x : Config k R} {ω : Noise k R} {r n t : ℕ} {w : Plane} {P : Fin k → ℤ}
    {st : State R j} (hV : ∀ l, st.1 l ∈ box r)
    (hpres : PresentAt (run x ω (t + 1)) w P st) (hclean : CleanAt ω t w P st)
    (hviol : st ∉ tables R j r (n + 1)) :
    ∃ Γ : Finset Plane, (∀ z ∈ Γ, z ∈ box r) ∧ Γ.card ≤ j ∧
    ∃ π : Plane → Plane, (∀ z ∈ Γ, z - π z ∈ box 1 ∧ ∃ l, π z = st.1 l) ∧
    ∃ I : Finset (Option (Fin k)), k + 1 ≤ I.card + j ∧
      ∀ i ∈ I, ∃ st' : State R j, (∀ l, st'.1 l ∈ Γ) ∧
        PresentAt (run x ω t) w (P + provider k i) st' ∧ st' ∉ tables R j r n := by
  classical
  set X' := run x ω t with hX'
  -- Step 1: a present tuple on the positions of `st` that fails the move round.
  have hQ : ¬ presentFamily (run x ω (t + 1)) w P (Set.range st.1) ⊆
      timed r (tables R j r n) := by
    intro h
    exact hviol (subset_inst h (presentFamily_closed _ w P _) ⟨fun l => ⟨l, rfl⟩, hpres⟩)
  obtain ⟨st₀, ⟨hpos₀, hpres₀⟩, hnot⟩ := Set.not_subset.mp hQ
  have hposV : ∀ l, st₀.1 l ∈ box r := by
    intro l
    obtain ⟨l', hl'⟩ := hpos₀ l
    rw [← hl']
    exact hV l'
  -- Step 2: common providers.
  have hq : ∀ l, k ≤ quorumCount (checkAll X') (w + st₀.1 l, P) (.live (st₀.2 l)) := by
    intro l
    obtain ⟨l', hl'⟩ := hpos₀ l
    have hev : (ω (t, (w + st₀.1 l, P))).1 = false := by rw [← hl']; exact hclean l'
    have h := hpres₀ l
    rw [run_succ, if_neg (by simp [hev])] at h
    exact quorumCount_of_quorumRule_eq_live h
  set I := Finset.univ.filter (fun i : Option (Fin k) =>
    ∀ l, checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l)) with hIdef
  have hfail : ∀ l, (Finset.univ.filter (fun i : Option (Fin k) =>
      ¬ checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l))).card ≤ 1 := by
    intro l
    have h1 := hq l
    have h2 := card_filter_not_add
      (fun i : Option (Fin k) => checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l))
    unfold quorumCount at h1
    simp only at h1 h2
    omega
  have hI : k + 1 ≤ I.card + j := by
    have hc := card_filter_not_add (fun i : Option (Fin k) =>
      ∀ l, checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l))
    have hsub : Finset.univ.filter (fun i : Option (Fin k) =>
        ¬ ∀ l, checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l)) ⊆
        Finset.univ.biUnion (fun l => Finset.univ.filter (fun i : Option (Fin k) =>
          ¬ checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l))) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
        Finset.mem_biUnion] at hi ⊢
      exact hi
    have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hsum : ∑ l : Fin j, (Finset.univ.filter (fun i : Option (Fin k) =>
        ¬ checkAll X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l))).card ≤
        ∑ _l : Fin j, 1 := Finset.sum_le_sum (fun l _ => hfail l)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hsum
    rw [← hIdef] at hc
    omega
  -- what the checker gives for `i ∈ I`
  have hkeep : ∀ i ∈ I, ∀ l, X' (w + st₀.1 l, P + provider k i) = .live (st₀.2 l) ∧
      ∀ d ∈ mooreDirs, ∃ s', X' (w + st₀.1 l + d, P + provider k i) = .live s' ∧
        Compatible (st₀.2 l) s' d := by
    intro i hi l
    simp only [hIdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact checker_live (hi l)
  -- Step 3: the parents.
  by_cases hS : st₀ ∈ tables R j r n
  · -- the move rule deletes `st₀`
    have hmv : ¬ MoveOK r (tables R j r n) st₀ := fun h => hnot ⟨hS, h⟩
    unfold MoveOK at hmv
    push Not at hmv
    obtain ⟨l, d, hd, hdV, hno⟩ := hmv
    refine ⟨Finset.univ.image (Function.update st₀.1 l (st₀.1 l + d)), ?_, ?_,
      fun z => if z = st₀.1 l + d then st₀.1 l else z, ?_, I, hI, ?_⟩
    · intro z hz
      obtain ⟨l', -, rfl⟩ := Finset.mem_image.mp hz
      rw [Function.update_apply]
      split_ifs
      · exact hdV
      · exact hposV l'
    · exact Finset.card_image_le.trans (by simp)
    · intro z hz
      obtain ⟨l', -, rfl⟩ := Finset.mem_image.mp hz
      by_cases hz' : Function.update st₀.1 l (st₀.1 l + d) l' = st₀.1 l + d
      · beta_reduce
        rw [if_pos hz', hz']
        refine ⟨by simpa using mem_box_one_of_mem_mooreDirs hd, ?_⟩
        obtain ⟨l'', hl''⟩ := hpos₀ l
        exact ⟨l'', hl''.symm⟩
      · beta_reduce
        rw [if_neg hz']
        refine ⟨by simpa [Prod.zero_eq_mk] using zero_mem_box_one, ?_⟩
        have hl' : l' ≠ l := by
          rintro rfl
          exact hz' (by simp)
        rw [Function.update_of_ne hl']
        obtain ⟨l'', hl''⟩ := hpos₀ l'
        exact ⟨l'', hl''.symm⟩
    · intro i hi
      obtain ⟨s', hs', hcomp⟩ := (hkeep i hi l).2 d hd
      refine ⟨move st₀ l d s', fun l' => Finset.mem_image_of_mem _ (Finset.mem_univ l'),
        fun l' => ?_, hno s' hcomp⟩
      simp only [move, Function.update_apply]
      split_ifs with hl'
      · subst hl'
        rw [← add_assoc]
        exact hs'
      · exact (hkeep i hi l').1
  · -- `st₀` itself violates `S_n`
    refine ⟨Finset.univ.image st₀.1, ?_, ?_, id, ?_, I, hI, ?_⟩
    · intro z hz
      obtain ⟨l', -, rfl⟩ := Finset.mem_image.mp hz
      exact hposV l'
    · exact Finset.card_image_le.trans (by simp)
    · intro z hz
      obtain ⟨l', -, rfl⟩ := Finset.mem_image.mp hz
      refine ⟨by simpa [Prod.zero_eq_mk] using zero_mem_box_one, ?_⟩
      obtain ⟨l'', hl''⟩ := hpos₀ l'
      exact ⟨l'', hl''.symm⟩
    · intro i hi
      exact ⟨st₀, fun l => Finset.mem_image_of_mem _ (Finset.mem_univ l),
        fun l => (hkeep i hi l).1, hS⟩

/-! ## `fgt:cover` and `fgt:live` -/

/-- **`fgt:cover`.** Let `k ≥ 2j`. Fix `x`, a noise realisation and the run `X` from `x`. If
`n ≤ t` and a pair with positions in `w + V` is present at `(P, t)` and violates `S^w_n`, then
`E_t(z_l, P) = 1` for some `l`, where `E` is the domination field of the replacement indicators. -/
theorem cover (hk : 2 * j ≤ k) (x : Config k R) (ω : Noise k R) (r : ℕ) :
    ∀ n t, n ≤ t → ∀ (w : Plane) (P : Fin k → ℤ) (st : State R j), (∀ l, st.1 l ∈ box r) →
      PresentAt (run x ω t) w P st → st ∉ tables R j r n →
        ∃ l, domField ω.flags t (w + st.1 l, P) := by
  classical
  intro n
  induction n with
  | zero =>
    intro t _ w P st hV hpres hviol
    exfalso
    have hsub : presentFamily (j := j) (run x ω t) w P (box r : Set Plane) ⊆ tables R j r 0 :=
      subset_inst (fun st' hst' => hst'.1) (presentFamily_closed _ w P _)
    exact hviol (hsub ⟨hV, hpres⟩)
  | succ n ih =>
    intro t ht w P st hV hpres hviol
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    by_cases hev : ∃ l, (ω (t, (w + st.1 l, P))).1 = true
    · obtain ⟨l, hl⟩ := hev
      exact ⟨l, (domField_succ _ _ _).mpr (Or.inl hl)⟩
    · have hclean : CleanAt ω t w P st := by
        intro l
        push Not at hev
        simpa using hev l
      obtain ⟨Γ, hΓV, -, π, hπ, I, hI, hpar⟩ := transport hV hpres hclean hviol
      obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
      haveI : Nonempty (State R j) := ⟨(hpar i₀ hi₀).choose⟩
      choose! sts hsts using hpar
      have hmark : ∀ i ∈ I, ∃ l, domField ω.flags t (w + (sts i).1 l, P + provider k i) :=
        fun i hi => ih t (by omega) w _ (sts i) (fun l => hΓV _ ((hsts i hi).1 l))
          (hsts i hi).2.1 (hsts i hi).2.2
      haveI : Nonempty (Fin j) := ⟨(hmark i₀ hi₀).choose⟩
      choose! ls hls using hmark
      -- pigeonhole on `i ↦ π(z'_i)`
      have hmaps : ∀ i ∈ I, π ((sts i).1 (ls i)) ∈ Finset.univ.image st.1 := by
        intro i hi
        obtain ⟨l, hl⟩ := (hπ _ ((hsts i hi).1 (ls i))).2
        rw [hl]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ l)
      have hcard : (Finset.univ.image st.1).card < I.card := by
        have := Finset.card_image_le (s := Finset.univ) (f := st.1)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨i, hi, i', hi', hne, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
      obtain ⟨hd, l₀, hl₀⟩ := hπ _ ((hsts i hi).1 (ls i))
      have hd' := (hπ _ ((hsts i' hi').1 (ls i'))).1
      rw [← heq, hl₀] at hd'
      rw [hl₀] at hd
      refine ⟨l₀, (domField_succ _ _ _).mpr (Or.inr ⟨i, i', hne, _, hd, _, hd', ?_, ?_⟩)⟩
      · have h := hls i hi
        convert h using 2
        simp only
        abel
      · have h := hls i' hi'
        convert h using 2
        simp only
        abel

/-- `0 ∈ V_r`. -/
theorem zero_mem_box (r : ℕ) : ((0 : Plane)) ∈ box r := by
  simp [box]

/-- **`fgt:live`.** Let `k ≥ 2j` and `S^{(r)}_τ(𝟎) = ∅`. For every `x`, every noise realisation,
every `t ≥ τ` and every site `v`, if `X_t(v)` is live then `E_t(v) = 1`. -/
theorem live_marked (hk : 2 * j ≤ k) {r τ : ℕ}
    (hτ : ∀ s : Fin j → LiveSymbol R, (origin, s) ∉ tables R j r τ)
    (x : Config k R) (ω : Noise k R) {t : ℕ} (ht : τ ≤ t) (v : Site k) (b : LiveSymbol R)
    (hb : run x ω t v = .live b) : domField ω.flags t v := by
  obtain ⟨l, hl⟩ := cover hk x ω r τ t ht v.1 v.2 (origin, fun _ => b)
    (fun _ => zero_mem_box r) (fun _ => by simpa [origin] using hb) (hτ _)
  simpa [origin] using hl

end FNE
