/-
# §9.2: repeated coarsening (`thr:dyadic`)

Hypotheses (`DyadicSetup`): `𝓛` is an arc-consistent list family, `m ≥ 1`,
`𝓛(y₁) = {𝔭₁}` and `𝓛(y₂) = {𝔭₂}` for opposite corner letters, `y₂ = y₁ + 2^m w`.
**[choice]** The opposite corner letters are written `(a, κ₁, A, β, β)` and `(a, κ₂, A, ¬β, ¬β)`
(`cornerLetter`), and `y₂ − y₁ ∈ 2^m ℤ²` is written with its quotient `w`.

The families `𝓛₀, …, 𝓛_m` are built explicitly (`levels`): `𝓛₀(z) = 𝓛(y₁ + z)` and
`𝓛_{k+1} = 𝓛_k↑`, where the phase of the coarsening is the one `thr:zero` gives from the pin
whose bit is `0` at level `k` (`zs`). Then:
* `thr:dyadic`(a): `levels_inv` (thin phase `0`, the two pins), `levels_setup` (the corner sets are
  singletons; the hypotheses of `thr:coarse`), `levels_family`, `levels_ac` (all levels);
* `thr:dyadic`(b): `levels_letters` (the letters of `𝓛_k(z)` come from those of `𝓛(y₁ + 2^k z)`
  by complementing both bits `k` times and putting the thin type of `𝓛_k` at `z`),
  `thin_base` (the latter have thin type `a`);
* `thr:dyadic`(c): `levels_top`;
* `thr:dyadic`(d): `levels_singleton`.
-/
import FixedNoiseErgodicity.Three.Coarse

set_option autoImplicit false

namespace FNE.Three

open FNE.Scaffold

/-! ## One coarsening step with the phase of a bit-0 corner letter -/

/-- One coarsening step, the corner sets being those of `thr:zero` for a corner letter with
bit `0` at `2 z₀` (thin phase `0`). -/
def stepL (L : Plane → Set Letter) (z0 : Plane) : Plane → Set Letter :=
  coarsen L 0 fun z => thinRule (z - z0)

theorem stepL_setup {L : Plane → Set Letter} {z0 : Plane} {κ : Corner} (hL : IsListFamily L)
    (hac : ArcConsistent L) (hc : HasThinPhase L 0) (hp : L (2 • z0) = {cornerLetter κ false}) :
    CoarseSetup L 0 (fun z => thinRule (z - z0)) where
  fam := hL
  ac := hac
  phase := hc
  angle_eq := thr_zero hL hac hc (by rwa [zero_add])

theorem stepL_apply (L : Plane → Set Letter) (z0 z : Plane) :
    stepL L z0 z = up (thinRule (z - z0)) '' L (2 • z) := by
  rw [stepL, coarsen, zero_add]

theorem up_cornerLetter (κ : Corner) (b : Bool) : up .a (cornerLetter κ b) = cornerLetter κ (!b) :=
  rfl

theorem thinRule_sub_two_smul (z u : Plane) : thinRule (z - 2 • u) = thinRule z := by
  rw [sub_eq_add_neg, ← smul_neg, thinRule_add_two_smul]

theorem two_pow_succ_smul (j : ℕ) (w : Plane) : 2 ^ (j + 1) • w = 2 • (2 ^ j • w) := by
  rw [pow_succ', mul_smul]

/-! ## The levels -/

/-- The hypotheses of `thr:dyadic`. -/
structure DyadicSetup (L : Plane → Set Letter) (m : ℕ) (y1 w : Plane) (κ1 κ2 : Corner)
    (β : Bool) : Prop where
  fam : IsListFamily L
  ac : ArcConsistent L
  m_pos : 1 ≤ m
  p1 : L y1 = {cornerLetter κ1 β}
  p2 : L (y1 + 2 ^ m • w) = {cornerLetter κ2 (!β)}

/-- The site `z₀` (with the bit-0 pin at `2 z₀`) at level `k`: the pin `1` (site `0`) if its bit
complemented `k` times is `0`, otherwise the pin `2` (site `2^{m-k} w`). -/
def zs (m : ℕ) (w : Plane) (β : Bool) (k : ℕ) : Plane :=
  if not^[k] β = false then 0 else 2 ^ (m - k - 1) • w

/-- `thr:dyadic`: the families `𝓛₀, …, 𝓛_m`. -/
def levels (L : Plane → Set Letter) (y1 w : Plane) (m : ℕ) (β : Bool) : ℕ → Plane → Set Letter
  | 0 => fun z => L (y1 + z)
  | k + 1 => stepL (levels L y1 w m β k) (zs m w β k)

theorem iterate_not_succ (k : ℕ) (b : Bool) : not^[k + 1] b = !(not^[k] b) :=
  Function.iterate_succ_apply' _ _ _

theorem iterate_not_not (k : ℕ) (b : Bool) : not^[k] (!b) = !(not^[k] b) := by
  rw [← Function.iterate_succ_apply, iterate_not_succ]

section Levels

variable {L : Plane → Set Letter} {m : ℕ} {y1 w : Plane} {κ1 κ2 : Corner} {β : Bool}

/-- The invariant of the induction in `thr:dyadic`, for `k < m`. -/
def LevelInv (L : Plane → Set Letter) (m : ℕ) (y1 w : Plane) (κ1 κ2 : Corner) (β : Bool)
    (k : ℕ) : Prop :=
  IsListFamily (levels L y1 w m β k) ∧ ArcConsistent (levels L y1 w m β k) ∧
    HasThinPhase (levels L y1 w m β k) 0 ∧
    levels L y1 w m β k 0 = {cornerLetter κ1 (not^[k] β)} ∧
    levels L y1 w m β k (2 ^ (m - k) • w) = {cornerLetter κ2 (not^[k] (!β))}

/-- At every level `k < m`, the pin with bit `0` sits at `2 z₀`. -/
theorem LevelInv.hp {k : ℕ} (hk : k < m) (J : LevelInv L m y1 w κ1 κ2 β k) :
    ∃ κ, levels L y1 w m β k (2 • zs m w β k) = {cornerLetter κ false} := by
  unfold zs
  split_ifs with h
  · exact ⟨κ1, by rw [smul_zero, J.2.2.2.1, h]⟩
  · refine ⟨κ2, ?_⟩
    rw [← two_pow_succ_smul, show m - k - 1 + 1 = m - k by omega, J.2.2.2.2, iterate_not_not]
    simp only [Bool.not_eq_false] at h
    rw [h]; rfl

/-- `thr:dyadic`(a): at every level `k < m` the hypotheses of `thr:coarse` hold. -/
theorem LevelInv.setup {k : ℕ} (hk : k < m) (J : LevelInv L m y1 w κ1 κ2 β k) :
    CoarseSetup (levels L y1 w m β k) 0 (fun z => thinRule (z - zs m w β k)) := by
  obtain ⟨κ, hp⟩ := J.hp hk
  exact stepL_setup J.1 J.2.1 J.2.2.1 hp

theorem zs_even {k : ℕ} (hk : k + 1 < m) : ∃ u, zs m w β k = 2 • u := by
  unfold zs
  split_ifs
  · exact ⟨0, (smul_zero _).symm⟩
  · refine ⟨2 ^ (m - k - 2) • w, ?_⟩
    rw [← two_pow_succ_smul, show m - k - 2 + 1 = m - k - 1 by omega]

theorem levels_inv (S : DyadicSetup L m y1 w κ1 κ2 β) : ∀ k < m, LevelInv L m y1 w κ1 κ2 β k := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨⟨fun z => S.fam.nonempty _, fun z => S.fam.inA _⟩, ?_, ?_, ?_, ?_⟩
    · intro z a ha d
      obtain ⟨b, hb, h⟩ := S.ac _ a ha d
      exact ⟨b, show b ∈ L (y1 + (z + d.vec)) by rwa [← add_assoc], h⟩
    · refine hasThinPhase_self (z0 := 0) ?_ ?_
      · intro z a ha d
        obtain ⟨b, hb, h⟩ := S.ac _ a ha d
        exact ⟨b, show b ∈ L (y1 + (z + d.vec)) by rwa [← add_assoc], h⟩
      · intro x hx
        change x ∈ L (y1 + 0) at hx
        rw [add_zero, S.p1, Set.mem_singleton_iff] at hx
        rw [hx]; rfl
    · change L (y1 + 0) = _
      rw [add_zero, S.p1]; rfl
    · change L (y1 + 2 ^ (m - 0) • w) = _
      rw [Nat.sub_zero, S.p2]; rfl
  | succ k ih =>
    have J := ih (by omega)
    have S' := J.setup (by omega)
    obtain ⟨u, hu⟩ := zs_even (w := w) (β := β) hk
    have hθ : ∀ z, thinRule (z - zs m w β k) = thinRule z := fun z => by
      rw [hu, thinRule_sub_two_smul]
    refine ⟨S'.coarsen_family, S'.coarsen_ac, ?_, ?_, ?_⟩
    · intro z x hx
      rw [CoarseSetup.coarsen_thin (L := levels L y1 w m β k) (c := 0)
        (θ := fun z => thinRule (z - zs m w β k)) z x hx, hθ, sub_zero]
    · change stepL _ _ 0 = _
      rw [stepL_apply, smul_zero, J.2.2.2.1, Set.image_singleton, hθ, thinRule_zero,
        up_cornerLetter, iterate_not_succ]
    · change stepL _ _ (2 ^ (m - (k + 1)) • w) = _
      have e1 : 2 • (2 ^ (m - (k + 1)) • w) = 2 ^ (m - k) • w := by
        rw [← two_pow_succ_smul, show m - (k + 1) + 1 = m - k by omega]
      have e2 : thinRule (2 ^ (m - (k + 1)) • w) = .a := by
        rw [show m - (k + 1) = (m - k - 2) + 1 by omega, two_pow_succ_smul,
          ← zero_add (2 • _), thinRule_add_two_smul]
        rfl
      rw [stepL_apply, e1, J.2.2.2.2, Set.image_singleton, hθ, e2, up_cornerLetter,
        iterate_not_succ]

/-- **`thr:dyadic`(c)**: for `r` the pin with bit `0` at level `m - 1` (site `z_r ∈ {0, w}`),
`𝓛_m` has thin phase `z_r` and `𝓛_m(z_r) = {(a, κ_r, A, 1, 1)}`. -/
theorem levels_top (S : DyadicSetup L m y1 w κ1 κ2 β) :
    ∃ zr κr, ((zr = 0 ∧ κr = κ1) ∨ (zr = w ∧ κr = κ2)) ∧
      HasThinPhase (levels L y1 w m β m) zr ∧
      levels L y1 w m β m zr = {cornerLetter κr true} := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := S.m_pos; omega⟩
  have J := levels_inv S k (by omega)
  refine ⟨zs (k + 1) w β k, ?_⟩
  unfold zs
  rw [show k + 1 - k - 1 = 0 by omega, pow_zero, one_smul]
  split_ifs with h
  · refine ⟨κ1, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro z x hx
      have := CoarseSetup.coarsen_thin (L := levels L y1 w (k + 1) β k) (c := 0)
        (θ := fun z => thinRule (z - zs (k + 1) w β k)) z x hx
      rwa [zs, if_pos h] at this
    · change stepL _ _ 0 = _
      rw [stepL_apply, smul_zero, J.2.2.2.1, Set.image_singleton, zs, if_pos h, sub_zero,
        thinRule_zero, up_cornerLetter, h]
      rfl
  · refine ⟨κ2, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro z x hx
      have := CoarseSetup.coarsen_thin (L := levels L y1 w (k + 1) β k) (c := 0)
        (θ := fun z => thinRule (z - zs (k + 1) w β k)) z x hx
      rwa [zs, if_neg h, show k + 1 - k - 1 = 0 by omega, pow_zero, one_smul] at this
    · change stepL _ _ w = _
      have e : 2 • w = 2 ^ (k + 1 - k) • w := by rw [show k + 1 - k = 1 by omega, pow_one]
      rw [stepL_apply, e, J.2.2.2.2, Set.image_singleton, zs, if_neg h,
        show k + 1 - k - 1 = 0 by omega, pow_zero, one_smul, sub_self, thinRule_zero,
        up_cornerLetter, iterate_not_not]
      simp only [Bool.not_eq_false] at h
      rw [h]; rfl

/-- `thr:dyadic`: every level `k ≤ m` is an arc-consistent list family. -/
theorem levels_family_ac (S : DyadicSetup L m y1 w κ1 κ2 β) {k : ℕ} (hk : k ≤ m) :
    IsListFamily (levels L y1 w m β k) ∧ ArcConsistent (levels L y1 w m β k) := by
  rcases Nat.lt_or_ge k m with h | h
  · exact ⟨(levels_inv S k h).1, (levels_inv S k h).2.1⟩
  · obtain rfl : k = m := le_antisymm hk h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := S.m_pos; omega⟩
    have S' := (levels_inv S j (by omega)).setup (by omega)
    exact ⟨S'.coarsen_family, S'.coarsen_ac⟩

/-- `thr:dyadic`(b), the letters: for `k ≥ 1`, `𝔞 ↦ 𝔞^{(k)}` complements both bits `k` times and
puts the thin type `t`. -/
def upk (t : Thin) (k : ℕ) (x : Letter) : Letter :=
  ⟨⟨t, x.base.thick, x.base.black⟩, not^[k] x.b1, not^[k] x.b2⟩

/-- **`thr:dyadic`(b)**: for `1 ≤ k`, `𝓛_k(z)` is the image of `𝓛(y₁ + 2^k z)` under complementing
both bits `k` times and putting the thin type of `𝓛_k` at `z`. (It holds for every `k ≥ 1`, without
hypotheses.) -/
theorem up_upk (t t' : Thin) (k : ℕ) (x : Letter) : up t (upk t' k x) = upk t (k + 1) x := by
  simp only [up, upk, iterate_not_succ]

theorem levels_letters (k : ℕ) (hk : 1 ≤ k) (z : Plane) :
    levels L y1 w m β k z =
      upk (thinRule (z - zs m w β (k - 1))) k '' L (y1 + 2 ^ k • z) := by
  induction k generalizing z with
  | zero => omega
  | succ k ih =>
    change stepL _ _ z = _
    rw [stepL_apply, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [show levels L y1 w m β 0 (2 • z) = L (y1 + 2 • z) from rfl, zero_add, pow_one]
      rfl
    · rw [ih hk' (2 • z), Set.image_image, smul_smul, ← pow_succ]
      congr 1
      funext x
      exact up_upk _ _ _ _

/-- **`thr:dyadic`(b)**: the letters of `𝓛(y₁ + 2^m z)` have thin type `a`. -/
theorem thin_base (S : DyadicSetup L m y1 w κ1 κ2 β) (z : Plane) :
    ∀ x ∈ L (y1 + 2 ^ m • z), x.base.thin = .a := by
  have hc : HasThinPhase L y1 :=
    hasThinPhase_self S.ac (by rw [S.p1]; rintro x rfl; rfl)
  intro x hx
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by have := S.m_pos; omega⟩
  rw [hc _ x hx, add_sub_cancel_left, hj, two_pow_succ_smul, ← zero_add (2 • _),
    thinRule_add_two_smul]
  rfl

/-- The blockwise substitution, one level: `(φ')^{l+1}(𝔠)(2y' + ς) = φ'((φ')^l(𝔠)(y'))(ς)`. -/
theorem phi'_iterate_fineSite (l : ℕ) (cc : Letter) (y' : Plane) (s1 s2 : Bool) :
    phi'^[l + 1] (fun _ => cc) (fineSite y' s1 s2) = (phi'^[l] (fun _ => cc) y').child s1 s2 := by
  rw [Function.iterate_succ_apply', phi', subst2_fineSite]

/-- **`thr:dyadic`(d)**: if `𝓛_m(z) = {𝔠}`, then `𝓛(y₁ + 2^m z + y) = {(φ')^m(𝔠)(y)}` for every
`y ∈ [0, 2^m)²`. -/
theorem levels_singleton (S : DyadicSetup L m y1 w κ1 κ2 β) {z : Plane} {cc : Letter}
    (h : levels L y1 w m β m z = {cc}) (y : Plane) (hy : y ∈ square 0 (2 ^ m)) :
    L (y1 + 2 ^ m • z + y) = {phi'^[m] (fun _ => cc) y} := by
  have key : ∀ l ≤ m, ∀ y ∈ square 0 (2 ^ l),
      levels L y1 w m β (m - l) (2 ^ l • z + y) = {phi'^[l] (fun _ => cc) y} := by
    intro l
    induction l with
    | zero =>
      intro _ y hy
      simp only [square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add, pow_zero,
        Nat.cast_one] at hy
      obtain ⟨y1', y2'⟩ := y
      obtain ⟨rfl, rfl⟩ : y1' = 0 ∧ y2' = 0 := by simp only at hy; omega
      rw [show (2 : ℕ) ^ 0 • z + ((0 : ℤ), (0 : ℤ)) = z by ext <;> simp, Nat.sub_zero, h]
      rfl
    | succ l ih =>
      intro hl y hy
      obtain ⟨y', s1, s2, rfl⟩ := exists_fineSite y
      have hy' : y' ∈ square 0 (2 ^ l) := by
        obtain ⟨a, b⟩ := y'
        simp only [square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add, fineSite,
          bitZ, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hy ⊢
        cases s1 <;> cases s2 <;> simp at hy <;> omega
      have Jk := (levels_inv S (m - (l + 1)) (by omega)).setup (by omega)
      have hsing := ih (by omega) y' hy'
      rw [show m - l = m - (l + 1) + 1 by omega] at hsing
      have := Jk.coarsen_singleton (2 ^ l • z + y') hsing s1 s2
      rw [phi'_iterate_fineSite]
      convert this using 2
      ext <;> simp [fineSite, pow_succ] <;> ring
  have := key m le_rfl y hy
  rw [Nat.sub_self] at this
  rw [add_assoc]
  exact this
end Levels

end FNE.Three
