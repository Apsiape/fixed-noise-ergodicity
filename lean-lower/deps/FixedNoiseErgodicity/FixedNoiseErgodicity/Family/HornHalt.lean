/-
# Section 6.6: `prop:horn`(c), the halting obstruction

If `M` halts with halting time `T`, no legal pattern of `T_M` on `[0,N)²`, `N ≥ 2T + 2`, has the
seed tile `s_M` at `(0,0)` (`horn_c`).

**[choice]** The field read off the pattern is `𝖦(ξ) = Θ_ξ(0,0)`, with `Θ_ξ` a legal block whose
tile is `Ξ(ξ)` (the printed proof uses `Θ_u(ξ − u)` for any `u`; every instance used mentions only
`ξ, ξ ± e₁, ξ + e₂`, which lie in the block at `ξ`, and the overlap property transfers the facts).
-/
import FixedNoiseErgodicity.Family.Horn

set_option autoImplicit false

namespace FNE.Family

open FNE

/-- 06:301 (overlap property, converse): equal east/west colours make two blocks agree on their
overlap of two columns. -/
theorem overlapE {Θ Θ' : FactField} (h : (tileOf Θ).E = (tileOf Θ').W) {y : Plane}
    (hy : y ∈ box 1) (hy0 : 0 ≤ y.1) : Θ y = Θ' (y - (1, 0)) := by
  have hb := (mem_box1 y).1 hy
  have h1 : y - (1, 0) ∈ box 1 := by
    rw [mem_box1]; simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]; omega
  ext F
  have := congrArg (fun c : Colour => (false, y, F) ∈ c) h
  simp only [tileOf] at this
  rw [mem_blockE, mem_blockW] at this
  simp only [hy, hy0, h1, hb.2.1, true_and] at this
  exact Iff.of_eq this

/-- 06:301 (overlap property, converse), vertically. -/
theorem overlapN {Θ Θ' : FactField} (h : (tileOf Θ).N = (tileOf Θ').S) {y : Plane}
    (hy : y ∈ box 1) (hy0 : 0 ≤ y.2) : Θ y = Θ' (y - (0, 1)) := by
  have hb := (mem_box1 y).1 hy
  have h1 : y - (0, 1) ∈ box 1 := by
    rw [mem_box1]; simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]; omega
  ext F
  have := congrArg (fun c : Colour => (true, y, F) ∈ c) h
  simp only [tileOf] at this
  rw [mem_blockN, mem_blockS] at this
  simp only [hy, hy0, h1, hb.2.2.2, true_and] at this
  exact Iff.of_eq this

/-- 06:301: the tile of a block determines the block on `Λ`. -/
theorem tileOf_eq_on {Θ Θ' : FactField} (h : tileOf Θ = tileOf Θ') {y : Plane}
    (hy : y ∈ box 1) : Θ y = Θ' y := by
  have hb := (mem_box1 y).1 hy
  ext F
  rcases le_or_gt 0 y.1 with hy0 | hy0
  · have := congrArg (fun c : Pay => (false, y, F) ∈ c.E) h
    simp only [tileOf] at this
    rw [mem_blockE, mem_blockE] at this
    simp only [hy, hy0, true_and] at this
    exact Iff.of_eq this
  · have := congrArg (fun c : Pay => (false, y + (1, 0), F) ∈ c.W) h
    simp only [tileOf] at this
    rw [mem_blockW, mem_blockW] at this
    have h2 : (y + (1, 0)).1 ≤ 1 := by simp only [Prod.fst_add]; omega
    simp only [add_sub_cancel_right, hy, h2, true_and] at this
    exact Iff.of_eq this

/-- The square `[0,N)²`. -/
def InSq (N : ℕ) (u : Plane) : Prop := 0 ≤ u.1 ∧ u.1 < N ∧ 0 ≤ u.2 ∧ u.2 < N

/-- **`prop:horn`(c).** If `M` halts with halting time `T` (the first time `M°` is in a halting
state), then for every `N ≥ 2T + 2` there is no legal pattern `Ξ` of `T_M` on `[0,N)²` with
`Ξ(0,0) = s_M`. -/
theorem horn_c (M : TuringMachine) (T : ℕ) (hT : oHalt M (oRun M T).state = true)
    (hmin : ∀ s < T, oHalt M (oRun M s).state = false) (N : ℕ) (hN : 2 * T + 2 ≤ N)
    (Ξ : Plane → Pay) (hΞ : ∀ u, InSq N u → InT M (Ξ u))
    (hE : ∀ u, InSq N u → InSq N (u + (1, 0)) → (Ξ u).E = (Ξ (u + (1, 0))).W)
    (hNS : ∀ u, InSq N u → InSq N (u + (0, 1)) → (Ξ u).N = (Ξ (u + (0, 1))).S)
    (h0 : Ξ (0, 0) = seedTile M) : False := by
  classical
  -- legal blocks under the tiles
  let Θ : Plane → FactField := fun u => if h : InT M (Ξ u) then h.choose else fun _ => ∅
  have hΘ : ∀ u, InSq N u → LegalFB M (Θ u) ∧ tileOf (Θ u) = Ξ u := fun u hu => by
    simp only [Θ, dif_pos (hΞ u hu)]; exact (hΞ u hu).choose_spec
  let G : Plane → Finset Fact := fun ξ => Θ ξ (0, 0)
  have hz : ((0 : ℤ), (0 : ℤ)) ∈ box 1 := by rw [mem_box1]; norm_num
  have hpE : ((1 : ℤ), (0 : ℤ)) ∈ box 1 := by rw [mem_box1]; norm_num
  have hpW : ((-1 : ℤ), (0 : ℤ)) ∈ box 1 := by rw [mem_box1]; norm_num
  have hpN : ((0 : ℤ), (1 : ℤ)) ∈ box 1 := by rw [mem_box1]; norm_num
  -- the block at `ξ` sees the neighbours' facts
  have trE : ∀ ξ, InSq N ξ → InSq N (ξ + (1, 0)) → Θ ξ (1, 0) = G (ξ + (1, 0)) := fun ξ h1 h2 => by
    have hm : (tileOf (Θ ξ)).E = (tileOf (Θ (ξ + (1, 0)))).W := by
      rw [(hΘ ξ h1).2, (hΘ _ h2).2]; exact hE ξ h1 h2
    rw [overlapE hm hpE (by norm_num), sub_self]; rfl
  have trW : ∀ ξ, InSq N (ξ - (1, 0)) → InSq N ξ → Θ ξ (-1, 0) = G (ξ - (1, 0)) :=
    fun ξ h1 h2 => by
      have e : ξ - (1, 0) + (1, 0) = ξ := sub_add_cancel _ _
      have hm : (tileOf (Θ (ξ - (1, 0)))).E = (tileOf (Θ ξ)).W := by
        rw [(hΘ _ h1).2, (hΘ _ h2).2]
        have := hE _ h1 (by rw [e]; exact h2)
        rwa [e] at this
      simp only [G]
      rw [overlapE hm hz le_rfl, Prod.mk_sub_mk]
      norm_num
  have trN : ∀ ξ, InSq N ξ → InSq N (ξ + (0, 1)) → Θ ξ (0, 1) = G (ξ + (0, 1)) := fun ξ h1 h2 => by
    have hm : (tileOf (Θ ξ)).N = (tileOf (Θ (ξ + (0, 1)))).S := by
      rw [(hΘ ξ h1).2, (hΘ _ h2).2]; exact hNS ξ h1 h2
    rw [overlapN hm hpN (by norm_num), sub_self]; rfl
  -- the clause instances at `(0,0)` of the block at `ξ`, in normal form
  have inst : ∀ ξ, InSq N ξ →
      (Fact.seed ∈ G ξ → Fact.P .wall ∈ G ξ) ∧
      (Fact.seed ∈ G ξ → Fact.start ∈ Θ ξ (1, 0)) ∧
      (Fact.start ∈ G ξ → Fact.P (.head .init OSym.blank) ∈ G ξ) ∧
      (Fact.start ∈ G ξ → Fact.ray ∈ Θ ξ (1, 0)) ∧
      (Fact.ray ∈ G ξ → Fact.P (.tape OSym.blank) ∈ G ξ) ∧
      (Fact.ray ∈ G ξ → Fact.ray ∈ Θ ξ (1, 0)) ∧
      (Fact.P .wall ∈ G ξ → Fact.P .wall ∈ Θ ξ (0, 1)) ∧
      (∀ a b c : MSym, Fact.P a ∈ Θ ξ (-1, 0) → Fact.P b ∈ G ξ → Fact.P c ∈ Θ ξ (1, 0) →
        Fact.P (next (oTr M) (oHalt M) a b c) ∈ Θ ξ (0, 1)) ∧
      (∀ (q : OState) (γ : OSym), oHalt M q = true → Fact.P (.head q γ) ∉ G ξ) := by
    intro ξ hξ
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := (hΘ ξ hξ).1.2 (0, 0)
    have hz' : ((0 : ℤ), (0 : ℤ)) ∈ (↑(box 1) : Set Plane) := hz
    have hE' : ((0 : ℤ), (0 : ℤ)) + (1, 0) ∈ (↑(box 1) : Set Plane) := by simpa using hpE
    have hW' : ((0 : ℤ), (0 : ℤ)) - (1, 0) ∈ (↑(box 1) : Set Plane) := by simpa using hpW
    have hN' : ((0 : ℤ), (0 : ℤ)) + (0, 1) ∈ (↑(box 1) : Set Plane) := by simpa using hpN
    exact ⟨i1 hz', fun h => by simpa using i2 hz' hE' h, i3 hz',
      fun h => by simpa using i4 hz' hE' h, i5 hz', fun h => by simpa using i6 hz' hE' h,
      fun h => by simpa using i7 hz' hN' h,
      fun a b c ha hb hc => by
        simpa using i8 hW' hz' hE' hN' a b c (by simpa using ha) hb (by simpa using hc),
      i9 hz'⟩
  have sq : ∀ x t : ℕ, x < N → t < N → InSq N ((x : ℤ), (t : ℤ)) := fun x t hx ht =>
    ⟨by simp, by simpa using hx, by simp, by simpa using ht⟩
  have sq0 : ∀ x : ℕ, x < N → InSq N ((x : ℤ), 0) := fun x hx => by simpa using sq x 0 hx (by omega)
  have e1 : ∀ (x : ℕ) (t : ℤ), ((x : ℤ), t) + (1, 0) = (((x + 1 : ℕ) : ℤ), t) := fun x t => by
    simp
  have e2 : ∀ (x : ℤ) (t : ℕ), (x, (t : ℤ)) + (0, 1) = (x, ((t + 1 : ℕ) : ℤ)) := fun x t => by
    simp
  -- the seed
  have hG0 : G (0, 0) = leastField M (0, 0) :=
    tileOf_eq_on (((hΘ (0, 0) (by simpa using sq0 0 (by omega))).2).trans h0) hz
  have hseed : Fact.seed ∈ G (0, 0) := by rw [hG0]; simp
  -- row `0`
  have row : ∀ x : ℕ, x ≤ 2 * T + 1 →
      Fact.P (CA M 0 x) ∈ G ((x : ℤ), 0) ∧ (2 ≤ x → Fact.ray ∈ G ((x : ℤ), 0)) ∧
        (x = 1 → Fact.start ∈ G ((x : ℤ), 0)) := by
    intro x hx
    induction x with
    | zero =>
      refine ⟨?_, by omega, by omega⟩
      rw [CA_zero_right]
      exact (inst _ (by simpa using sq0 0 (by omega))).1 (by simpa using hseed)
    | succ x ih =>
      have ih := ih (by omega)
      have hs := sq0 x (by omega)
      have hs1 := sq0 (x + 1) (by omega)
      have hs' : InSq N (((x : ℤ), 0) + (1, 0)) := by rw [e1]; exact hs1
      have tr := trE _ hs hs'
      rw [e1] at tr
      have I := inst _ hs
      have J := inst _ hs1
      rcases Nat.lt_or_ge x 1 with hx0 | hx1
      · obtain rfl : x = 0 := by omega
        have hst : Fact.start ∈ G (((0 + 1 : ℕ) : ℤ), 0) := by
          rw [← tr]; exact I.2.1 (by simpa using hseed)
        refine ⟨?_, by omega, fun _ => hst⟩
        rw [CA_zero_one]
        exact J.2.2.1 hst
      · have hray : Fact.ray ∈ G (((x + 1 : ℕ) : ℤ), 0) := by
          rw [← tr]
          rcases Nat.lt_or_ge x 2 with hx2 | hx2
          · obtain rfl : x = 1 := by omega
            exact I.2.2.2.1 (ih.2.2 rfl)
          · exact I.2.2.2.2.2.1 (ih.2.1 hx2)
        refine ⟨?_, fun _ => hray, fun h => by omega⟩
        obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
        rw [show n + 1 + 1 = n + 2 by omega, CA_zero_add_two]
        exact J.2.2.2.2.1 hray
  -- column `0`: the wall
  have col : ∀ t : ℕ, t ≤ T → Fact.P .wall ∈ G (0, (t : ℤ)) := by
    intro t ht
    induction t with
    | zero => simpa [CA_zero_right] using (row 0 (by omega)).1
    | succ t ih =>
      have hs : InSq N (0, (t : ℤ)) := by simpa using sq 0 t (by omega) (by omega)
      have hs' : InSq N ((0, (t : ℤ)) + (0, 1)) := by
        rw [e2]; simpa using sq 0 (t + 1) (by omega) (by omega)
      have := (inst _ hs).2.2.2.2.2.2.1 (ih (by omega))
      rw [trN _ hs hs', e2] at this
      exact this
  -- the computation, by (H8)
  have comp : ∀ t : ℕ, t ≤ T → ∀ x : ℕ, 1 ≤ x → x ≤ 2 * T + 1 - t →
      Fact.P (CA M t x) ∈ G ((x : ℤ), (t : ℤ)) := by
    intro t
    induction t with
    | zero => intro _ x _ hx; simpa using (row x (by omega)).1
    | succ t ih =>
      intro ht x hx1 hx2
      have ih := ih (by omega)
      obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
      have hs := sq (n + 1) t (by omega) (by omega)
      have hsW : InSq N ((((n + 1 : ℕ) : ℤ), (t : ℤ)) - (1, 0)) := by
        have eW : (((n + 1 : ℕ) : ℤ), (t : ℤ)) - (1, 0) = ((n : ℤ), (t : ℤ)) := by simp
        rw [eW]; exact sq n t (by omega) (by omega)
      have hsE : InSq N ((((n + 1 : ℕ) : ℤ), (t : ℤ)) + (1, 0)) := by
        rw [e1]; exact sq (n + 1 + 1) t (by omega) (by omega)
      have hsN : InSq N ((((n + 1 : ℕ) : ℤ), (t : ℤ)) + (0, 1)) := by
        rw [e2]; exact sq (n + 1) (t + 1) (by omega) (by omega)
      have ha : Fact.P (CA M t n) ∈ Θ (((n + 1 : ℕ) : ℤ), (t : ℤ)) (-1, 0) := by
        rw [trW _ hsW hs]
        have eW : (((n + 1 : ℕ) : ℤ), (t : ℤ)) - (1, 0) = ((n : ℤ), (t : ℤ)) := by simp
        rw [eW]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [CA_zero_right]; simpa using col t (by omega)
        · exact ih n hn (by omega)
      have hb : Fact.P (CA M t (n + 1)) ∈ G (((n + 1 : ℕ) : ℤ), (t : ℤ)) :=
        ih (n + 1) (by omega) (by omega)
      have hc : Fact.P (CA M t (n + 2)) ∈ Θ (((n + 1 : ℕ) : ℤ), (t : ℤ)) (1, 0) := by
        rw [trE _ hs hsE, e1]; exact ih (n + 1 + 1) (by omega) (by omega)
      have := (inst _ hs).2.2.2.2.2.2.2.1 _ _ _ ha hb hc
      rw [← CA_succ_succ, trN _ hs hsN, e2] at this
      exact this
  -- the halting head violates (H9)
  obtain ⟨x, q, γ, hx1, hx2, hCA, hq⟩ := CA_halt M T hT hmin
  have hP := comp T le_rfl x hx1 (by omega)
  rw [hCA] at hP
  exact (inst _ (sq x T (by omega) (by omega))).2.2.2.2.2.2.2.2 q γ hq hP

end FNE.Family
