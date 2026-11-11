/-
# Section 6.4: `fam:positive`(b) for rows

For the routed tiling of `fam:positive`(a) (phase `(1/3, 1/3)`): a tile is a horizontal carrier
iff `ξ₁` lies in the interior of a frame of depth `own(ξ₂)`. Proof as printed: the walls of the
row are the endpoints of the frames of the depths `d` with `ξ₂` in a frame of depth `d`; the frame
of depth `own(ξ₂)` around `ξ₁` contains no other wall (`no_wall_inside`), and conversely nearest
walls `left, right` bound a frame of depth `own(ξ₂)` (the nesting argument of `fam:laminar`,
specialised to frames: `row_carrier_mp`).
-/
import FixedNoiseErgodicity.Family.Routing

set_option autoImplicit false

namespace FNE.Family

open FNE.Scaffold

variable {f : ℕ → Plane → Letter}

/-- `fam:positive` (proof): inside a frame of depth `own(z)` the row `z` carries no light vertical
wall (a wall is an endpoint of a frame of a depth `e ≥ own(z)`; equal depth contradicts
`fam:frames`(a), first claim, and larger depth its second claim). -/
theorem no_wall_inside (hf : IsInfTower (diag third) f) {z m w : ℤ}
    (h1 : frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < w)
    (h2 : w < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m) :
    rowWall f z w = none := by
  by_contra hne
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨e, he, hend, hin⟩ := (rowWall_iff hf z w s).1 hs
  have hle := own_le _ forall_inFrame_third he hin
  have hend' : IsLeftEnd (towerOffsets third) e w ∨ IsRightEnd (towerOffsets third) e w :=
    hend.imp And.right And.right
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hn := endpoint_not_inFrame (frameOffsets_tower third) hlt
    rcases hend' with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact (hn n).1 ⟨m, h1.le, h2.le⟩
    · exact (hn n).2 ⟨m, h1.le, h2.le⟩
  · rw [← heq] at hend'
    rcases hend' with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have := frame_window_unique ⟨h1.le, h2.le⟩
        ⟨le_rfl, (frameLo_lt_frameHi (towerOffsets third) _ n).le⟩
      subst this; exact lt_irrefl _ h1
    · have := frame_window_unique ⟨h1.le, h2.le⟩
        ⟨(frameLo_lt_frameHi (towerOffsets third) _ n).le, le_rfl⟩
      subst this; exact lt_irrefl _ h2

theorem lineFlow_eq_empty_iff {W : ℤ → Option Side} {hW : ∀ n : ℤ, ∃ k : ℕ, W (n - k) ≠ none}
    {hE : ∀ n : ℤ, ∃ k : ℕ, W (n + 1 + k) ≠ none} (e : ℤ) :
    lineFlow W hW hE e = Flow.empty ↔
      W (westWall W hW e) = some .lo ∧ W (eastWall W hE e) = some .hi := by
  unfold lineFlow
  generalize W (westWall W hW e) = a
  generalize W (eastWall W hE e) = b
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> simp [Flow.empty]

/-- `fam:positive`(b), the converse direction for rows: inside a frame of depth `own(z)` the nearest
walls are its endpoints, a left side and a right side. -/
theorem row_carrier_mpr (hf : IsInfTower (diag third) f) {z x m : ℤ}
    (h1 : frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < x)
    (h2 : x < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m) :
    rowWall f z (westWall (rowWall f z) (rowWall_west hf z) x) = some .lo ∧
      rowWall f z (eastWall (rowWall f z) (rowWall_east hf z) x) = some .hi := by
  obtain ⟨hd, hz⟩ := own_spec _ forall_inFrame_third z
  have hL := (rowWall_iff hf z _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hz⟩
  have hR := (rowWall_iff hf z _ .hi).2 ⟨_, hd, Or.inr ⟨rfl, m, rfl⟩, hz⟩
  rw [westWall_eq h1.le (by rw [hL]; simp) (fun w' hw1 hw2 => no_wall_inside hf hw1 (by omega)),
    eastWall_eq h2 (by rw [hR]; simp) (fun w' hw1 hw2 => no_wall_inside hf (by omega) hw2)]
  exact ⟨hL, hR⟩

/-- `fam:positive`(b), the direct direction for rows: if `ξ₁` is not a wall and its nearest walls
are a left side (west) and a right side (east), then `ξ₁` lies in the interior of a frame of
depth `own(z)` (the argument of `fam:laminar`, with `fam:frames`(a),(b)). -/
theorem row_carrier_mp (hf : IsInfTower (diag third) f) {z x : ℤ} (hx : rowWall f z x = none)
    (hw1 : rowWall f z (westWall (rowWall f z) (rowWall_west hf z) x) = some .lo)
    (hw2 : rowWall f z (eastWall (rowWall f z) (rowWall_east hf z) x) = some .hi) :
    ∃ m, frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < x ∧
      x < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m := by
  have ha := frameOffsets_tower third
  set w1 := westWall (rowWall f z) (rowWall_west hf z) x with hw1def
  set w2 := eastWall (rowWall f z) (rowWall_east hf z) x with hw2def
  have hw1x : w1 < x := by
    rcases lt_or_eq_of_le (westWall_le (hW := rowWall_west hf z) x) with h | h
    · exact h
    · rw [← hw1def] at h; rw [h, hx] at hw1; cases hw1
  have hxw2 : x < w2 := lt_eastWall (hE := rowWall_east hf z) x
  -- no wall strictly between `w₁` and `w₂`
  have hgap : ∀ w', w1 < w' → w' < w2 → rowWall f z w' = none := by
    intro w' h1 h2
    rcases le_or_gt w' x with h | h
    · exact westWall_max h1 h
    · exact eastWall_min h h2
  have isWall : ∀ {w : ℤ} {s : Side}, rowWall f z w = some s → w1 < w → w2 ≤ w := by
    intro w s hs h1
    by_contra h2
    rw [hgap w h1 (by omega)] at hs; cases hs
  -- `w₁` is the left endpoint of a frame `I_e(m)` with `e ≥ own(z)`
  obtain ⟨e, he, hend, hin⟩ := (rowWall_iff hf z _ .lo).1 hw1
  obtain ⟨m, hm⟩ : IsLeftEnd (towerOffsets third) e w1 := by
    rcases hend with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · cases h
  have hle := own_le _ forall_inFrame_third he hin
  set d0 := own _ forall_inFrame_third z with hd0
  obtain ⟨hd0pos, hz0⟩ := own_spec _ forall_inFrame_third z
  have hR' := (rowWall_iff hf z _ .hi).2 ⟨e, he, Or.inr ⟨rfl, m, rfl⟩, hin⟩
  have hlt' := frameLo_lt_frameHi (towerOffsets third) e m
  have hR'w2 : w2 ≤ frameHi (towerOffsets third) e m := isWall hR' (by omega)
  -- `w₂` is the right endpoint of a frame `I_{e''}(m'')`, whose left endpoint is `≤ w₁`
  obtain ⟨e'', he'', hend'', hin''⟩ := (rowWall_iff hf z _ .hi).1 hw2
  obtain ⟨m'', hm''⟩ : IsRightEnd (towerOffsets third) e'' w2 := by
    rcases hend'' with ⟨h, -⟩ | ⟨-, h⟩
    · cases h
    · exact h
  have hL'' := (rowWall_iff hf z _ .lo).2 ⟨e'', he'', Or.inl ⟨rfl, m'', rfl⟩, hin''⟩
  have hlt'' := frameLo_lt_frameHi (towerOffsets third) e'' m''
  have hL''w1 : frameLo (towerOffsets third) e'' m'' ≤ w1 := by
    by_contra h
    have := isWall hL'' (by omega)
    omega
  -- `e = own(z)`
  have he0 : e = d0 := by
    by_contra hne
    have hlt : d0 < e := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨m', hc1, hc2⟩ := frames_contain (towerOffsets third) hlt m
    have hn := frames_nested ha hlt m m'
    have hj := frameLo_lt_frameHi (towerOffsets third) d0 m'
    have hjl : frameLo (towerOffsets third) d0 m' < frameHi (towerOffsets third) e m := by omega
    have hJ := (rowWall_iff hf z _ .lo).2 ⟨d0, hd0pos, Or.inl ⟨rfl, m', rfl⟩, hz0⟩
    have hjw2 : w2 ≤ frameLo (towerOffsets third) d0 m' := isWall hJ (by omega)
    rcases lt_trichotomy e'' e with h | h | h
    · have := frames_nested ha h m m''; omega
    · subst h
      have := frame_window_unique (m := m) (m' := m'') (z := w1) ⟨by omega, by omega⟩
        ⟨hL''w1, by omega⟩
      subst this
      omega
    · have := frames_nested ha h m'' m; omega
  subst he0
  exact ⟨m, by omega, by omega⟩

/-- **`fam:positive`(b)**, rows, for the routed tiling of `fam:positive`(a): the tile at `ξ` is a
horizontal carrier iff `ξ₁ ∈ I̊_d(m)` for `d = own(ξ₂)` and some `m`. -/
theorem positive_b_row (hf : IsInfTower (diag third) f) (ξ : Plane) :
    (routedTiling hf ξ).HCarrier ↔ ∃ m,
      frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.2) m < ξ.1 ∧
        ξ.1 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.2) m := by
  have hrules := lineFlow_rules (W := rowWall f ξ.2) (hW := rowWall_west hf ξ.2)
    (hE := rowWall_east hf ξ.2) ξ.1
  unfold RTile.HCarrier routedTiling
  dsimp only
  cases hx : rowWall f ξ.2 ξ.1 with
  | some s =>
    rw [hx] at hrules
    refine ⟨fun h => absurd h (not_carrier_of_wall hrules), fun ⟨m, h1, h2⟩ => ?_⟩
    rw [no_wall_inside hf h1 h2] at hx; cases hx
  | none =>
    rw [hx] at hrules
    simp only [FlowRules] at hrules
    rw [hrules, and_self, lineFlow_eq_empty_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact row_carrier_mp hf hx h1 h2
    · rintro ⟨m, h1, h2⟩; exact row_carrier_mpr hf h1 h2

/-- `fam:positive` (proof): inside a frame of depth `own(z)` the column `z` carries no light horizontal
wall (a wall is an endpoint of a frame of a depth `e ≥ own(z)`; equal depth contradicts
`fam:frames`(a), first claim, and larger depth its second claim). -/
theorem no_wall_inside_col (hf : IsInfTower (diag third) f) {z m w : ℤ}
    (h1 : frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < w)
    (h2 : w < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m) :
    colWall f z w = none := by
  by_contra hne
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨e, he, hend, hin⟩ := (colWall_iff hf z w s).1 hs
  have hle := own_le _ forall_inFrame_third he hin
  have hend' : IsLeftEnd (towerOffsets third) e w ∨ IsRightEnd (towerOffsets third) e w :=
    hend.imp And.right And.right
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hn := endpoint_not_inFrame (frameOffsets_tower third) hlt
    rcases hend' with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact (hn n).1 ⟨m, h1.le, h2.le⟩
    · exact (hn n).2 ⟨m, h1.le, h2.le⟩
  · rw [← heq] at hend'
    rcases hend' with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have := frame_window_unique ⟨h1.le, h2.le⟩
        ⟨le_rfl, (frameLo_lt_frameHi (towerOffsets third) _ n).le⟩
      subst this; exact lt_irrefl _ h1
    · have := frame_window_unique ⟨h1.le, h2.le⟩
        ⟨(frameLo_lt_frameHi (towerOffsets third) _ n).le, le_rfl⟩
      subst this; exact lt_irrefl _ h2

/-- `fam:positive`(b), the converse direction for columns: inside a frame of depth `own(z)` the nearest
walls are its endpoints, a left side and a right side. -/
theorem col_carrier_mpr (hf : IsInfTower (diag third) f) {z x m : ℤ}
    (h1 : frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < x)
    (h2 : x < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m) :
    colWall f z (westWall (colWall f z) (colWall_south hf z) x) = some .lo ∧
      colWall f z (eastWall (colWall f z) (colWall_north hf z) x) = some .hi := by
  obtain ⟨hd, hz⟩ := own_spec _ forall_inFrame_third z
  have hL := (colWall_iff hf z _ .lo).2 ⟨_, hd, Or.inl ⟨rfl, m, rfl⟩, hz⟩
  have hR := (colWall_iff hf z _ .hi).2 ⟨_, hd, Or.inr ⟨rfl, m, rfl⟩, hz⟩
  rw [westWall_eq h1.le (by rw [hL]; simp) (fun w' hw1 hw2 => no_wall_inside_col hf hw1 (by omega)),
    eastWall_eq h2 (by rw [hR]; simp) (fun w' hw1 hw2 => no_wall_inside_col hf (by omega) hw2)]
  exact ⟨hL, hR⟩

/-- `fam:positive`(b), the direct direction for columns: if `ξ₂` is not a wall and its nearest walls
are a bottom side (south) and a top side (north), then `ξ₂` lies in the interior of a frame of
depth `own(z)` (the argument of `fam:laminar`, with `fam:frames`(a),(b)). -/
theorem col_carrier_mp (hf : IsInfTower (diag third) f) {z x : ℤ} (hx : colWall f z x = none)
    (hw1 : colWall f z (westWall (colWall f z) (colWall_south hf z) x) = some .lo)
    (hw2 : colWall f z (eastWall (colWall f z) (colWall_north hf z) x) = some .hi) :
    ∃ m, frameLo (towerOffsets third) (own _ forall_inFrame_third z) m < x ∧
      x < frameHi (towerOffsets third) (own _ forall_inFrame_third z) m := by
  have ha := frameOffsets_tower third
  set w1 := westWall (colWall f z) (colWall_south hf z) x with hw1def
  set w2 := eastWall (colWall f z) (colWall_north hf z) x with hw2def
  have hw1x : w1 < x := by
    rcases lt_or_eq_of_le (westWall_le (hW := colWall_south hf z) x) with h | h
    · exact h
    · rw [← hw1def] at h; rw [h, hx] at hw1; cases hw1
  have hxw2 : x < w2 := lt_eastWall (hE := colWall_north hf z) x
  -- no wall strictly between `w₁` and `w₂`
  have hgap : ∀ w', w1 < w' → w' < w2 → colWall f z w' = none := by
    intro w' h1 h2
    rcases le_or_gt w' x with h | h
    · exact westWall_max h1 h
    · exact eastWall_min h h2
  have isWall : ∀ {w : ℤ} {s : Side}, colWall f z w = some s → w1 < w → w2 ≤ w := by
    intro w s hs h1
    by_contra h2
    rw [hgap w h1 (by omega)] at hs; cases hs
  -- `w₁` is the left endpoint of a frame `I_e(m)` with `e ≥ own(z)`
  obtain ⟨e, he, hend, hin⟩ := (colWall_iff hf z _ .lo).1 hw1
  obtain ⟨m, hm⟩ : IsLeftEnd (towerOffsets third) e w1 := by
    rcases hend with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · cases h
  have hle := own_le _ forall_inFrame_third he hin
  set d0 := own _ forall_inFrame_third z with hd0
  obtain ⟨hd0pos, hz0⟩ := own_spec _ forall_inFrame_third z
  have hR' := (colWall_iff hf z _ .hi).2 ⟨e, he, Or.inr ⟨rfl, m, rfl⟩, hin⟩
  have hlt' := frameLo_lt_frameHi (towerOffsets third) e m
  have hR'w2 : w2 ≤ frameHi (towerOffsets third) e m := isWall hR' (by omega)
  -- `w₂` is the right endpoint of a frame `I_{e''}(m'')`, whose left endpoint is `≤ w₁`
  obtain ⟨e'', he'', hend'', hin''⟩ := (colWall_iff hf z _ .hi).1 hw2
  obtain ⟨m'', hm''⟩ : IsRightEnd (towerOffsets third) e'' w2 := by
    rcases hend'' with ⟨h, -⟩ | ⟨-, h⟩
    · cases h
    · exact h
  have hL'' := (colWall_iff hf z _ .lo).2 ⟨e'', he'', Or.inl ⟨rfl, m'', rfl⟩, hin''⟩
  have hlt'' := frameLo_lt_frameHi (towerOffsets third) e'' m''
  have hL''w1 : frameLo (towerOffsets third) e'' m'' ≤ w1 := by
    by_contra h
    have := isWall hL'' (by omega)
    omega
  -- `e = own(z)`
  have he0 : e = d0 := by
    by_contra hne
    have hlt : d0 < e := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨m', hc1, hc2⟩ := frames_contain (towerOffsets third) hlt m
    have hn := frames_nested ha hlt m m'
    have hj := frameLo_lt_frameHi (towerOffsets third) d0 m'
    have hjl : frameLo (towerOffsets third) d0 m' < frameHi (towerOffsets third) e m := by omega
    have hJ := (colWall_iff hf z _ .lo).2 ⟨d0, hd0pos, Or.inl ⟨rfl, m', rfl⟩, hz0⟩
    have hjw2 : w2 ≤ frameLo (towerOffsets third) d0 m' := isWall hJ (by omega)
    rcases lt_trichotomy e'' e with h | h | h
    · have := frames_nested ha h m m''; omega
    · subst h
      have := frame_window_unique (m := m) (m' := m'') (z := w1) ⟨by omega, by omega⟩
        ⟨hL''w1, by omega⟩
      subst this
      omega
    · have := frames_nested ha h m'' m; omega
  subst he0
  exact ⟨m, by omega, by omega⟩

/-- **`fam:positive`(b)**, columns, for the routed tiling of `fam:positive`(a): the tile at `ξ` is a
vertical carrier iff `ξ₂ ∈ I̊_d(m)` for `d = own(ξ₁)` and some `m`. -/
theorem positive_b_col (hf : IsInfTower (diag third) f) (ξ : Plane) :
    (routedTiling hf ξ).VCarrier ↔ ∃ m,
      frameLo (towerOffsets third) (own _ forall_inFrame_third ξ.1) m < ξ.2 ∧
        ξ.2 < frameHi (towerOffsets third) (own _ forall_inFrame_third ξ.1) m := by
  have hrules := lineFlow_rules (W := colWall f ξ.1) (hW := colWall_south hf ξ.1)
    (hE := colWall_north hf ξ.1) ξ.2
  unfold RTile.VCarrier routedTiling
  dsimp only
  cases hx : colWall f ξ.1 ξ.2 with
  | some s =>
    rw [hx] at hrules
    refine ⟨fun h => absurd h (not_carrier_of_wall hrules), fun ⟨m, h1, h2⟩ => ?_⟩
    rw [no_wall_inside_col hf h1 h2] at hx; cases hx
  | none =>
    rw [hx] at hrules
    simp only [FlowRules] at hrules
    rw [hrules, and_self, lineFlow_eq_empty_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact col_carrier_mp hf hx h1 h2
    · rintro ⟨m, h1, h2⟩; exact col_carrier_mpr hf h1 h2

end FNE.Family
