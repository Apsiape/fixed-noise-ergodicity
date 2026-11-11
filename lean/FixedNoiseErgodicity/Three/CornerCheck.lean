/-
# §9.3, the corner lemma: the statement, the restriction lemma, and a sound checker

* The finite statement of `thr:corner` (09:211): the thin-type rule of thin phase `0`
  (`thinRule`), the lists `𝒟_κ(v)` (`InD`), and consistency on a box (`ConsistentOn`).
* **The restriction lemma** (planning note 1): a family consistent on a set `U` is consistent
  on every `U' ⊆ U` (`ConsistentOn.anti`); the lists `𝒟_κ(v)` are defined from `κ` and `v` alone,
  not from the box (`InD` has no box parameter), so a sub-box sees the same constraints.
* The checker (`BLUEPRINT.md`, Part E). Sites of `V_6` are indices `j < 169` in raster order
  (`site`, `nbr`); a state is a list of 169 masks of 276 bits (bit `i` is the letter
  `letterAt i`). The certificate is a list of updates `(j, e, m)`, each checked against the
  current state: the neighbour of `j` in direction `e` lies in the box, and `m` contains every
  letter of the mask at `j` that has a fitting letter in the mask of that neighbour
  (`stepOK`); then the mask at `j` becomes `m`. The supporting letters are computed from the
  colour-class masks (`supp`): the letters fitting a letter in direction `e` form one colour
  class.
* Soundness (`inv_runCheck`): if `K` is consistent on `V_6` and `K(v) ⊆ 𝒟_κ(v)`, then every state
  of an accepted run contains `K`. So if the last state misses the root at the centre,
  `K(0) = ∅` (`corner_of_certOK`).

Nothing about the data is trusted: the kernel evaluates `certOK κ` in `Three/Corner.lean`.
-/
import FixedNoiseErgodicity.Three.CornerTables

set_option autoImplicit false

set_option maxRecDepth 20000

namespace FNE.Three

open FNE.Scaffold

/-! ## The finite statement (09:211) -/

/-- 09:97, 09:211: the thin type `a`, `c`, `d` or `b` according as `v` is congruent to `(0,0)`,
`(1,0)`, `(0,1)` or `(1,1)` modulo `2` (the rule of thin phase `0`). -/
def thinRule (v : Plane) : Thin :=
  if v.1 % 2 = 0 then (if v.2 % 2 = 0 then .a else .d) else (if v.2 % 2 = 0 then .c else .b)

/-- 09:211: the lists `𝒟_κ(v)`. `𝒟_κ(0) = {(a, κ, A, 1, 1)}`; for `v ≠ 0`, the letters of `𝔸`
whose thin type is given by `thinRule v`, except the four corner letters `(a, κ', A, 0, 0)`.
**[choice]** Lists are predicates on letters; they are read only on the box. -/
def InD (κ : Corner) (v : Plane) (x : Letter) : Prop :=
  if v = 0 then x = cornerLetter κ true
  else x.InA ∧ x.base.thin = thinRule v ∧ ∀ κ' : Corner, x ≠ cornerLetter κ' false

/-- 09:211: a family `𝒦` is *consistent on* `U` if for every `v ∈ U`, every `𝔞 ∈ 𝒦(v)` and every
direction `e` with `v + e ∈ U`, some `𝔟 ∈ 𝒦(v + e)` fits `𝔞` in direction `e`. Neighbours outside
`U` impose nothing. **[choice]** Families are total maps `ℤ² → Set Letter`, read on `U`. -/
def ConsistentOn (U : Set Plane) (K : Plane → Set Letter) : Prop :=
  ∀ v ∈ U, ∀ a ∈ K v, ∀ d : Dir, v + d.vec ∈ U → ∃ b ∈ K (v + d.vec), a.Fits d b

/-- **The restriction lemma** (planning note 1, session 5): consistency on `U` gives
consistency on every subset of `U`, in particular on a centred sub-box. -/
theorem ConsistentOn.anti {U U' : Set Plane} {K : Plane → Set Letter} (h : ConsistentOn U K)
    (hU : U' ⊆ U) : ConsistentOn U' K :=
  fun v hv a ha d hd => h v (hU hv) a ha d (hU hd)

theorem InD.inA {κ : Corner} {v : Plane} {x : Letter} (h : InD κ v x) : x.InA := by
  unfold InD at h
  split_ifs at h
  · subst h; exact cornerLetter_inA κ true
  · exact h.1

/-! ## Sites of `V_6` -/

/-- The site of index `j` in `V_6`: `(j mod 13 − 6, ⌊j / 13⌋ − 6)` (raster order). -/
def site (j : ℕ) : Plane := (((j % 13 : ℕ) : ℤ) - 6, ((j / 13 : ℕ) : ℤ) - 6)

theorem site_mem {j : ℕ} (hj : j < 169) : site j ∈ (box 6 : Set Plane) := by
  rw [Finset.mem_coe, mem_box_iff]
  simp only [site]
  omega

theorem exists_site {v : Plane} (hv : v ∈ (box 6 : Set Plane)) : ∃ j < 169, site j = v := by
  rw [Finset.mem_coe, mem_box_iff] at hv
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v.1 + 6 by omega)
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ v.2 + 6 by omega)
  refine ⟨b * 13 + a, by omega, ?_⟩
  ext <;> simp only [site] <;> omega

theorem site_inj {j j' : ℕ} (h : site j = site j') : j = j' := by
  simp only [site, Prod.mk.injEq] at h
  omega

theorem site_centre : site 84 = 0 := by
  simp [site]

theorem site_ne_zero {j : ℕ} (h : j ≠ 84) : site j ≠ 0 := fun h' =>
  h (site_inj (h'.trans site_centre.symm))

/-- The neighbour of index `j` in direction `d`, if it lies in `V_6`. -/
def nbr (j : ℕ) : Dir → Option ℕ
  | .e1 => if j % 13 < 12 then some (j + 1) else none
  | .e1' => if 0 < j % 13 then some (j - 1) else none
  | .e2 => if j < 156 then some (j + 13) else none
  | .e2' => if 13 ≤ j then some (j - 13) else none

theorem nbr_spec {j j' : ℕ} {d : Dir} (hj : j < 169) (h : nbr j d = some j') :
    j' < 169 ∧ site j' = site j + d.vec := by
  cases d <;> simp only [nbr] at h <;> split_ifs at h <;> simp only [Option.some.injEq] at h <;>
    subst h <;> refine ⟨by omega, ?_⟩ <;> ext <;> simp only [site, Dir.vec, Prod.fst_add,
      Prod.snd_add] <;> omega

/-- The thin type of the site of index `j`, computed on `ℕ`. -/
def thinOf (j : ℕ) : Thin :=
  if j % 13 % 2 = 0 then (if j / 13 % 2 = 0 then .a else .d) else (if j / 13 % 2 = 0 then .c else .b)

theorem thinOf_eq (j : ℕ) : thinOf j = thinRule (site j) := by
  have h1 : (((j % 13 : ℕ) : ℤ) - 6) % 2 = 0 ↔ j % 13 % 2 = 0 := by omega
  have h2 : (((j / 13 : ℕ) : ℤ) - 6) % 2 = 0 ↔ j / 13 % 2 = 0 := by omega
  simp only [thinOf, thinRule, site, h1, h2]

/-! ## Supporting letters from colour classes -/

/-- The union of the first masks of the pairs whose second mask meets `A`. -/
def supp : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: ps, A => if p.2 &&& A = 0 then supp ps A else p.1 ||| supp ps A

theorem testBit_supp {ps : List (ℕ × ℕ)} {A : ℕ} {p : ℕ × ℕ} (hp : p ∈ ps) (h : p.2 &&& A ≠ 0)
    {i : ℕ} (hi : p.1.testBit i = true) : (supp ps A).testBit i = true := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [supp, if_neg h, Nat.testBit_or, hi, Bool.true_or]
    · rw [supp]
      split_ifs
      · exact ih hp
      · rw [Nat.testBit_or, ih hp, Bool.or_true]

/-- For direction `d`: the pairs (class of code `c` on the side of `𝔞` facing `d`, class of
code `c` on the opposite side), read from the literal tables; pairs with an empty class are
dropped (they support nothing; 40 of the 64 codes remain on each side). -/
def pairs (d : Dir) : List (ℕ × ℕ) :=
  (match d with
    | .e1 => clsE.zip clsW
    | .e1' => clsW.zip clsE
    | .e2 => clsN.zip clsS
    | .e2' => clsS.zip clsN).filter fun p => p.1 != 0 && p.2 != 0

theorem codeV_lt (c : (VAtom × VAtom × Bool) × Bool) : codeV c < 64 := by
  obtain ⟨⟨a, b, x⟩, y⟩ := c
  have := a.code_lt; have := b.code_lt; have := x.toNat_lt; have := y.toNat_lt
  simp only [codeV]
  omega

theorem codeH_lt (c : (HAtom × HAtom × Bool) × Bool) : codeH c < 64 := by
  obtain ⟨⟨a, b, x⟩, y⟩ := c
  have := a.code_lt; have := b.code_lt; have := x.toNat_lt; have := y.toNat_lt
  simp only [codeH]
  omega

/-- Every colour code is `< 64`, so `64` class masks per side cover all codes. -/
theorem Letter.code_lt (s : Side) (x : Letter) : x.code s < 64 := by
  cases s
  exacts [codeV_lt _, codeH_lt _, codeV_lt _, codeH_lt _]

theorem testBit_classMask (s : Side) (c : ℕ) (i : Fin 276) :
    (classMask s c).testBit i = ((letterAt i).code s == c) :=
  testBit_letterMask _ i

theorem pair_mem {s t : Side} {c : ℕ} (hc : c < 64) (h1 : classMask s c ≠ 0)
    (h2 : classMask t c ≠ 0) :
    (classMask s c, classMask t c) ∈ (((List.range 64).map (classMask s)).zip
      ((List.range 64).map (classMask t))).filter fun p => p.1 != 0 && p.2 != 0 := by
  rw [List.zip_map', List.mem_filter]
  exact ⟨List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩, by simp [h1, h2]⟩

theorem ne_zero_of_testBit {x i : ℕ} (h : x.testBit i = true) : x ≠ 0 := by
  rintro rfl; simp at h

theorem land_ne_zero {x y : ℕ} {i : ℕ} (hx : x.testBit i = true) (hy : y.testBit i = true) :
    x &&& y ≠ 0 := by
  intro h
  have := congrArg (fun n => n.testBit i) h
  simp [Nat.testBit_and, hx, hy] at this

/-- **Supporting letters.** If the letter `i'` lies in `A` and fits the letter `i` in direction
`d`, then `i` lies in `supp (pairs d) A`. -/
theorem testBit_supp_of_fits {d : Dir} {A : ℕ} {i i' : Fin 276} (hA : A.testBit i' = true)
    (hf : (letterAt i).Fits d (letterAt i')) : (supp (pairs d) A).testBit i = true := by
  rw [← fitCode_iff] at hf
  cases d <;> simp only [fitCode, beq_iff_eq] at hf <;>
    simp only [pairs, clsN_eq, clsE_eq, clsS_eq, clsW_eq]
  · have h1 : (classMask .E (letterAt i).codeE).testBit i = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq]
    have h2 : (classMask .W (letterAt i).codeE).testBit i' = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq, hf]
    exact testBit_supp (pair_mem (Letter.code_lt .E (letterAt i)) (ne_zero_of_testBit h1)
      (ne_zero_of_testBit h2)) (land_ne_zero h2 hA) h1
  · have h1 : (classMask .W (letterAt i).codeW).testBit i = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq]
    have h2 : (classMask .E (letterAt i).codeW).testBit i' = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq, hf]
    exact testBit_supp (pair_mem (Letter.code_lt .W (letterAt i)) (ne_zero_of_testBit h1)
      (ne_zero_of_testBit h2)) (land_ne_zero h2 hA) h1
  · have h1 : (classMask .N (letterAt i).codeN).testBit i = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq]
    have h2 : (classMask .S (letterAt i).codeN).testBit i' = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq, hf]
    exact testBit_supp (pair_mem (Letter.code_lt .N (letterAt i)) (ne_zero_of_testBit h1)
      (ne_zero_of_testBit h2)) (land_ne_zero h2 hA) h1
  · have h1 : (classMask .S (letterAt i).codeS).testBit i = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq]
    have h2 : (classMask .N (letterAt i).codeS).testBit i' = true := by
      simp only [testBit_classMask, Letter.code, beq_iff_eq, hf]
    exact testBit_supp (pair_mem (Letter.code_lt .S (letterAt i)) (ne_zero_of_testBit h1)
      (ne_zero_of_testBit h2)) (land_ne_zero h2 hA) h1

/-! ## The checker -/

/-- The letters of the mask at `j` that have a fitting letter in the mask of the neighbour in
direction `d` (`0` if that neighbour lies outside the box: such an update is rejected). -/
def kept (st : List ℕ) (j : ℕ) (d : Dir) : ℕ :=
  match nbr j d with
  | none => 0
  | some j' => st.getD j 0 &&& supp (pairs d) (st.getD j' 0)

/-- An update `(j, d, m)` is accepted if the neighbour in direction `d` lies in the box and `m`
contains every letter of the mask at `j` supported in direction `d`. -/
def stepOK (st : List ℕ) (j : ℕ) (d : Dir) (m : ℕ) : Bool :=
  (nbr j d).isSome && (kept st j d &&& m) == kept st j d

/-- Run the updates in order, checking each against the current state. -/
def runCheck : List ℕ → List (ℕ × Dir × ℕ) → Option (List ℕ)
  | st, [] => some st
  | st, u :: rest => if stepOK st u.1 u.2.1 u.2.2 then runCheck (st.set u.1 u.2.2) rest else none

/-- The initial state: the masks of `𝒟_κ`. -/
def init (κ : Corner) : List ℕ :=
  (List.range 169).map fun j => if j = 84 then 2 ^ rootIdx κ else dMask (thinOf j)

/-- The certificate for the corner `κ` is accepted: every update is accepted, and the last state
misses the root at the centre (index `84`). -/
def certOK (κ : Corner) : Bool :=
  match runCheck (init κ) (ups κ) with
  | some st => !((st.getD 84 0).testBit (rootIdx κ))
  | none => false

/-! ## Soundness -/

/-- The invariant: the state contains `K` on the box. -/
def Inv (K : Plane → Set Letter) (st : List ℕ) : Prop :=
  ∀ j < 169, ∀ i : Fin 276, letterAt i ∈ K (site j) → (st.getD j 0).testBit i = true

section Soundness

variable {K : Plane → Set Letter}

theorem stepOK_testBit {st : List ℕ} (hInv : Inv K st) (hK : ConsistentOn (box 6) K)
    (hA : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, x.InA) {j : ℕ} {d : Dir} {m : ℕ}
    (h : stepOK st j d m = true) (hj : j < 169) {i : Fin 276} (hi : letterAt i ∈ K (site j)) :
    m.testBit i = true := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨j', hnb⟩, h⟩ := h
  have hk : (kept st j d).testBit i = true := by
    rw [kept, hnb]
    obtain ⟨hj', hs⟩ := nbr_spec hj hnb
    have hmem : site j + d.vec ∈ (box 6 : Set Plane) := hs ▸ site_mem hj'
    obtain ⟨b, hb, hfit⟩ := hK _ (site_mem hj) _ hi d hmem
    obtain ⟨i', rfl⟩ := exists_letterAt (hA _ hmem b hb)
    rw [Nat.testBit_and, hInv j hj i hi, Bool.true_and]
    exact testBit_supp_of_fits (hInv j' hj' i' (hs ▸ hb)) hfit
  have := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_and, hk, Bool.true_and] at this
  exact this

theorem getD_set (l : List ℕ) (j j0 m : ℕ) :
    (l.set j m).getD j0 0 = if j = j0 ∧ j0 < l.length then m else l.getD j0 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = j0
  · subst h
    by_cases h' : j < l.length
    · simp [h']
    · simp [h', List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

theorem inv_set {st : List ℕ} (hInv : Inv K st) (hK : ConsistentOn (box 6) K)
    (hA : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, x.InA) {j : ℕ} {d : Dir} {m : ℕ}
    (h : stepOK st j d m = true) : Inv K (st.set j m) := by
  intro j0 hj0 i hi
  rw [getD_set]
  split_ifs with hj
  · obtain ⟨rfl, -⟩ := hj
    exact stepOK_testBit hInv hK hA h hj0 hi
  · exact hInv j0 hj0 i hi

theorem inv_runCheck (hK : ConsistentOn (box 6) K)
    (hA : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, x.InA) :
    ∀ (us : List (ℕ × Dir × ℕ)) (st st' : List ℕ), Inv K st → runCheck st us = some st' →
      Inv K st'
  | [], st, st', hInv, h => by
    simp only [runCheck, Option.some.injEq] at h; exact h ▸ hInv
  | u :: us, st, st', hInv, h => by
    simp only [runCheck] at h
    split_ifs at h with hok
    exact inv_runCheck hK hA us _ _ (inv_set hInv hK hA hok) h

theorem init_getD (κ : Corner) {j : ℕ} (hj : j < 169) :
    (init κ).getD j 0 = if j = 84 then 2 ^ rootIdx κ else dMask (thinOf j) := by
  rw [init, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem inv_init {κ : Corner} (hD : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, InD κ v x) :
    Inv K (init κ) := by
  intro j hj i hi
  have hInD := hD _ (site_mem hj) _ hi
  rw [init_getD κ hj]
  split_ifs with h84
  · subst h84
    rw [site_centre, InD, if_pos rfl, ← letterAt_rootIdx κ] at hInD
    rw [letterAt_injective hInD]
    exact Nat.testBit_two_pow_self
  · rw [InD, if_neg (site_ne_zero h84)] at hInD
    obtain ⟨-, hθ, hz⟩ := hInD
    rw [dMask_eq, testBit_letterMask, dPred, thinOf_eq, ← hθ]
    have : zeroCornerB (letterAt i) = false := by
      rw [Bool.eq_false_iff, ne_eq, zeroCornerB_iff]
      rintro ⟨κ', h⟩
      exact hz κ' h
    simp [this]

/-- **Soundness of the certificate.** If `certOK κ` holds, every family consistent on `V_6` and
contained in `𝒟_κ` has `𝒦(0) = ∅`. -/
theorem corner_of_certOK {κ : Corner} (hc : certOK κ = true) (hK : ConsistentOn (box 6) K)
    (hD : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, InD κ v x) : K 0 = ∅ := by
  have hA : ∀ v ∈ (box 6 : Set Plane), ∀ x ∈ K v, x.InA := fun v hv x hx => InD.inA (hD v hv x hx)
  unfold certOK at hc
  split at hc
  · rename_i st hrun
    have hInv := inv_runCheck hK hA _ _ _ (inv_init hD) hrun
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have h0 : x = cornerLetter κ true := by
      have := hD 0 (by rw [Finset.mem_coe, mem_box_iff]; simp) x hx
      rwa [InD, if_pos rfl] at this
    rw [h0, ← letterAt_rootIdx κ, ← site_centre] at hx
    have := hInv 84 (by norm_num) _ hx
    rw [this] at hc
    exact absurd hc (by simp)
  · exact absurd hc (by simp)

end Soundness

end FNE.Three
