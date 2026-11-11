/-
# §9.3: the list-family cores of `thr:promote` and `thr:word`

The printed lemmas are about corner pairs, pin pairs of the plane-safe set `𝒲` (token level).
Their proofs apply `thr:dyadic` and `thr:corner-plane` to the walker lists `𝓛_𝐩` of a corner
pair, which are arc consistent with singletons at the pins (`thr:lists`, not yet formalized).
Here are those list-family steps, stated for any list family with the hypotheses of
`thr:dyadic`; the token-level lemmas will be short wrappers once `thr:lists` is in place.
* `promote_lists` (core of `thr:promote`): one of the pins, `𝓛(y_r) = {𝔭_r}`, and a corner
  letter of the opposite bit in `𝓛(y')` with `y' − y_r ∈ 2^{m+1} ℤ²`.
* `word_lists` (core of `thr:word`): for `m = 2n`, `𝓛(y_r + y) = {σⁿ(𝔞)(y)}` on `[0, 4ⁿ)²`, with
  `𝔞 = (a, κ_r, A, 1, 1)`.
-/
import FixedNoiseErgodicity.Three.Dyadic

set_option autoImplicit false

namespace FNE.Three

open FNE.Scaffold

theorem iterate_not_injective (m : ℕ) : Function.Injective (not^[m]) :=
  Function.Injective.iterate (fun _ _ h => Bool.not_inj h) m

section Pairs

variable {L : Plane → Set Letter} {m : ℕ} {y1 w : Plane} {κ1 κ2 : Corner} {β : Bool}

/-- The pin of `thr:dyadic`(c) in the original family. -/
theorem pin_of_top {zr : Plane} {κr : Corner} {βr : Bool} (S : DyadicSetup L m y1 w κ1 κ2 β)
    (h : (zr = 0 ∧ κr = κ1 ∧ βr = β) ∨ (zr = w ∧ κr = κ2 ∧ βr = !β)) :
    L (y1 + 2 ^ m • zr) = {cornerLetter κr βr} := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [smul_zero, add_zero, S.p1]
  · exact S.p2

/-- **Core of `thr:promote`.** Under the hypotheses of `thr:dyadic` (order `m`), for one of the
pins, `𝓛(y_r) = {𝔭_r}` with `y_r = y₁ + 2^m z_r`, and some `𝓛(y')` with
`y' = y₁ + 2^m (z_r + 2u)`, so `y' − y_r ∈ 2^{m+1} ℤ²`, contains the corner letter of the bit
opposite to that of `𝔭_r`. -/
theorem promote_lists (S : DyadicSetup L m y1 w κ1 κ2 β) :
    ∃ zr κr βr, ((zr = 0 ∧ κr = κ1 ∧ βr = β) ∨ (zr = w ∧ κr = κ2 ∧ βr = !β)) ∧
      L (y1 + 2 ^ m • zr) = {cornerLetter κr βr} ∧
      ∃ u κ', cornerLetter κ' (!βr) ∈ L (y1 + 2 ^ m • (zr + 2 • u)) := by
  obtain ⟨zr, κr, hor, hc, hroot⟩ := levels_top S
  obtain ⟨βr, hor'⟩ : ∃ βr, (zr = 0 ∧ κr = κ1 ∧ βr = β) ∨ (zr = w ∧ κr = κ2 ∧ βr = !β) := by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨β, Or.inl ⟨h1, h2, rfl⟩⟩
    · exact ⟨!β, Or.inr ⟨h1, h2, rfl⟩⟩
  have hpin := pin_of_top S hor'
  refine ⟨zr, κr, βr, hor', hpin, ?_⟩
  obtain ⟨LF, AC⟩ := levels_family_ac S le_rfl
  obtain ⟨v, -, κ', hκ'⟩ := corner_plane LF AC hroot
  -- `v` is even: the letter has thin type `a`
  have hthin := hc _ _ hκ'
  rw [add_sub_cancel_left] at hthin
  obtain ⟨v1, v2⟩ := v
  have hev : v1 % 2 = 0 ∧ v2 % 2 = 0 := by
    simp only [thinRule] at hthin
    split_ifs at hthin with h1 h2 <;> first | exact ⟨h1, h2⟩ | exact absurd hthin (by simp [cornerLetter])
  refine ⟨(v1 / 2, v2 / 2), κ', ?_⟩
  have hv : (v1, v2) = 2 • (v1 / 2, v2 / 2) := by
    ext <;> simp only [two_nsmul, Prod.fst_add, Prod.snd_add] <;> omega
  -- pull the letter back to `𝓛` (`thr:dyadic`(b))
  rw [levels_letters m S.m_pos] at hκ' hroot
  obtain ⟨b0, hb0, hup⟩ := hκ'
  rw [hpin, Set.image_singleton, Set.singleton_eq_singleton_iff] at hroot
  have hroot' : not^[m] βr = true := congrArg Letter.b1 hroot
  have hbit : not^[m] b0.b1 = false := congrArg Letter.b1 hup
  have hκ : b0.base.thick = .corner κ' := congrArg (fun x => x.base.thick) hup
  have hb0A := S.fam.inA _ _ hb0
  have hb0a := thin_base S (zr + (v1, v2)) b0 hb0
  obtain ⟨κ'', hκ''⟩ := Letter.InA.eq_cornerLetter hb0A ⟨hb0a, by rw [hκ]; trivial⟩
  rw [hκ''] at hκ hb0
  simp only [cornerLetter, Thick.corner.injEq] at hκ
  subst hκ
  have : b0.b1 = !βr := iterate_not_injective m (by rw [hbit, iterate_not_not, hroot']; rfl)
  rw [← this, ← hv]
  exact hb0

/-- **Core of `thr:word`.** Under the hypotheses of `thr:dyadic` with `m = 2n`, for one of the
pins `y_r = y₁ + 4ⁿ z_r` and `𝔞 = (a, κ_r, A, 1, 1)`, `𝓛(y_r + y) = {σⁿ(𝔞)(y)}` for every
`y ∈ [0, 4ⁿ)²`. -/
theorem word_lists {n : ℕ} (S : DyadicSetup L (2 * n) y1 w κ1 κ2 β) :
    ∃ zr κr, ((zr = 0 ∧ κr = κ1) ∨ (zr = w ∧ κr = κ2)) ∧
      ∀ y ∈ square 0 (4 ^ n), L (y1 + 4 ^ n • zr + y) = {sigmaPow n (cornerLetter κr true) y} := by
  obtain ⟨zr, κr, hor, -, hroot⟩ := levels_top S
  refine ⟨zr, κr, hor, fun y hy => ?_⟩
  have e : (2 : ℕ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have := levels_singleton S hroot y (by rwa [e])
  rwa [phi'_iterate_two_mul, e] at this

end Pairs

end FNE.Three
