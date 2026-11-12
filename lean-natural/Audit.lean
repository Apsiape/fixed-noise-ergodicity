/-
# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)

Prints and strictly audits every root of `ForgettingNaturalRule/Audit.lean` (the five release targets
first), then checks the axioms of every imported declaration of the development and of the imported
modules of the three reused cores (`FixedNoiseErgodicity.*`, `UndecidablePhaseDiagram.*`,
`UncomputableNoiseDiagram.*`), including private and generated ones: only `propext`, `Classical.choice`,
`Quot.sound` are allowed, and no such declaration is an axiom. Finally it checks the types of the five
release targets, and of the two conditional forms kept in the development.
(Modelled on the noise-diagram, hard-model and forgetting relays' package `Audit.lean`.)
-/
import ForgettingNaturalRule
import UncomputableNoiseDiagram.AuditCommand

set_option autoImplicit false

#print axioms FNR.natural_classification
#audit_axioms_strict FNR.natural_classification
#print axioms FNR.theorem_A
#audit_axioms_strict FNR.theorem_A
#print axioms FNR.machine_corollary
#audit_axioms_strict FNR.machine_corollary
#print axioms FNR.domino_reduction
#audit_axioms_strict FNR.domino_reduction
#print axioms FNR.domino_undecidable
#audit_axioms_strict FNR.domino_undecidable
#print axioms FNR.theorem_A_from_domino
#audit_axioms_strict FNR.theorem_A_from_domino
#print axioms FNR.theorem_A_undecidable
#audit_axioms_strict FNR.theorem_A_undecidable
#print axioms FNR.ergodicity_reduction
#audit_axioms_strict FNR.ergodicity_reduction
#print axioms FNR.ergodicity_undecidable
#audit_axioms_strict FNR.ergodicity_undecidable
#print axioms FNR.Const.Delta_eq
#audit_axioms_strict FNR.Const.Delta_eq
#print axioms FNR.Const.B_eq
#audit_axioms_strict FNR.Const.B_eq
#print axioms FNR.Const.B_ge
#audit_axioms_strict FNR.Const.B_ge
#print axioms FNR.Const.epsStar_eq
#audit_axioms_strict FNR.Const.epsStar_eq
#print axioms FNR.Const.epsStar_pos
#audit_axioms_strict FNR.Const.epsStar_pos
#print axioms FNR.Const.epsStar_le_one
#audit_axioms_strict FNR.Const.epsStar_le_one
#print axioms FNR.Const.four_le_Kc_pow
#audit_axioms_strict FNR.Const.four_le_Kc_pow
#print axioms FNR.Const.four_mul_pow_le
#audit_axioms_strict FNR.Const.four_mul_pow_le
#print axioms FNR.Const.Kc_mul_le
#audit_axioms_strict FNR.Const.Kc_mul_le
#print axioms FNR.Rule.chkI_eq_some
#audit_axioms_strict FNR.Rule.chkI_eq_some
#print axioms FNR.Rule.mem_cardinal_zero
#audit_axioms_strict FNR.Rule.mem_cardinal_zero
#print axioms FNR.Rule.mem_cardinal_e1
#audit_axioms_strict FNR.Rule.mem_cardinal_e1
#print axioms FNR.Rule.mem_cardinal_w1
#audit_axioms_strict FNR.Rule.mem_cardinal_w1
#print axioms FNR.Rule.mem_cardinal_e2
#audit_axioms_strict FNR.Rule.mem_cardinal_e2
#print axioms FNR.Rule.mem_cardinal_w2
#audit_axioms_strict FNR.Rule.mem_cardinal_w2
#print axioms FNR.Rule.plane_add_zero
#audit_axioms_strict FNR.Rule.plane_add_zero
#print axioms FNR.Rule.cardinal_sub_box
#audit_axioms_strict FNR.Rule.cardinal_sub_box
#print axioms FNR.Rule.chkI_congr
#audit_axioms_strict FNR.Rule.chkI_congr
#print axioms FNR.Rule.quorum_unique
#audit_axioms_strict FNR.Rule.quorum_unique
#print axioms FNR.Rule.GI_eq_some_iff
#audit_axioms_strict FNR.Rule.GI_eq_some_iff
#print axioms FNR.Rule.card_failed_le
#audit_axioms_strict FNR.Rule.card_failed_le
#print axioms FNR.Rule.GI_congr
#audit_axioms_strict FNR.Rule.GI_congr
#print axioms FNR.Rule.disc_parent
#audit_axioms_strict FNR.Rule.disc_parent
#print axioms FNR.Rule.chkI_clone_inputs
#audit_axioms_strict FNR.Rule.chkI_clone_inputs
#print axioms FNR.Rule.GI_live_centres
#audit_axioms_strict FNR.Rule.GI_live_centres
#print axioms FNR.Rule.card_bad_of_ne_clone
#audit_axioms_strict FNR.Rule.card_bad_of_ne_clone
#print axioms FNR.Rule.twoCl_of_card
#audit_axioms_strict FNR.Rule.twoCl_of_card
#print axioms FNR.Rule.siteEquiv_site
#audit_axioms_strict FNR.Rule.siteEquiv_site
#print axioms FNR.Rule.siteEquiv_symm
#audit_axioms_strict FNR.Rule.siteEquiv_symm
#print axioms FNR.Rule.site_zero
#audit_axioms_strict FNR.Rule.site_zero
#print axioms FNR.Rule.corner_eq
#audit_axioms_strict FNR.Rule.corner_eq
#print axioms FNR.Rule.offset_eq
#audit_axioms_strict FNR.Rule.offset_eq
#print axioms FNR.Rule.symm_shift
#audit_axioms_strict FNR.Rule.symm_shift
#print axioms FNR.Rule.site_add
#audit_axioms_strict FNR.Rule.site_add
#print axioms FNR.Rule.check_translate
#audit_axioms_strict FNR.Rule.check_translate
#print axioms FNR.Rule.natMap_translate
#audit_axioms_strict FNR.Rule.natMap_translate
#print axioms FNR.Rule.natMap_eq
#audit_axioms_strict FNR.Rule.natMap_eq
#print axioms FNR.Rule.natMap_local
#audit_axioms_strict FNR.Rule.natMap_local
#print axioms FNR.Rule.natCA_apply
#audit_axioms_strict FNR.Rule.natCA_apply
#print axioms FNR.Rule.dec_update
#audit_axioms_strict FNR.Rule.dec_update
#print axioms FNR.Rule.dec_inj
#audit_axioms_strict FNR.Rule.dec_inj
#print axioms FNR.Rule.isTraj_of_complete
#audit_axioms_strict FNR.Rule.isTraj_of_complete
#print axioms FNR.Rule.complete_flag_eq
#audit_axioms_strict FNR.Rule.complete_flag_eq
#print axioms FNR.Rule.isTraj_flow
#audit_axioms_strict FNR.Rule.isTraj_flow
#print axioms FNR.Rule.flowTraj_zero
#audit_axioms_strict FNR.Rule.flowTraj_zero
#print axioms FNR.Rule.flowTraj_nat
#audit_axioms_strict FNR.Rule.flowTraj_nat
#print axioms FNR.Coh.UL.gi
#audit_axioms_strict FNR.Coh.UL.gi
#print axioms FNR.Coh.keepsI_live
#audit_axioms_strict FNR.Coh.keepsI_live
#print axioms FNR.Coh.ul_of_good
#audit_axioms_strict FNR.Coh.ul_of_good
#print axioms FNR.Coh.ul_nbr_of_good
#audit_axioms_strict FNR.Coh.ul_nbr_of_good
#print axioms FNR.Coh.coh_rel
#audit_axioms_strict FNR.Coh.coh_rel
#print axioms FNR.Coh.coh_back
#audit_axioms_strict FNR.Coh.coh_back
#print axioms FNR.Coh.ul_down
#audit_axioms_strict FNR.Coh.ul_down
#print axioms FNR.Coh.ul_move
#audit_axioms_strict FNR.Coh.ul_move
#print axioms FNR.Coh.add_pair
#audit_axioms_strict FNR.Coh.add_pair
#print axioms FNR.Coh.ul_reach
#audit_axioms_strict FNR.Coh.ul_reach
#print axioms FNR.Coh.ul_common
#audit_axioms_strict FNR.Coh.ul_common
#print axioms FNR.Coh.ul_same
#audit_axioms_strict FNR.Coh.ul_same
#print axioms FNR.Coh.ul_east
#audit_axioms_strict FNR.Coh.ul_east
#print axioms FNR.Coh.ul_north
#audit_axioms_strict FNR.Coh.ul_north
#print axioms FNR.Coh.tiles_of_UL
#audit_axioms_strict FNR.Coh.tiles_of_UL
#print axioms FNR.Coh.live_marked
#audit_axioms_strict FNR.Coh.live_marked
#print axioms FNR.Forget.Delta_pos
#audit_axioms_strict FNR.Forget.Delta_pos
#print axioms FNR.Forget.base_le
#audit_axioms_strict FNR.Forget.base_le
#print axioms FNR.Forget.enc_le
#audit_axioms_strict FNR.Forget.enc_le
#print axioms FNR.Forget.pathEv_null_nat
#audit_axioms_strict FNR.Forget.pathEv_null_nat
#print axioms FNR.Forget.raw_paths_nat
#audit_axioms_strict FNR.Forget.raw_paths_nat
#print axioms FNR.Forget.tsum_pow_succ_le
#audit_axioms_strict FNR.Forget.tsum_pow_succ_le
#print axioms FNR.Forget.root_bound
#audit_axioms_strict FNR.Forget.root_bound
#print axioms FNR.Forget.disc_step
#audit_axioms_strict FNR.Forget.disc_step
#print axioms FNR.Forget.disc_path
#audit_axioms_strict FNR.Forget.disc_path
#print axioms FNR.Forget.unique_complete
#audit_axioms_strict FNR.Forget.unique_complete
#print axioms FNR.Forget.ergodic_of_not_tiles
#audit_axioms_strict FNR.Forget.ergodic_of_not_tiles
#print axioms FNR.Memory.traj_succ
#audit_axioms_strict FNR.Memory.traj_succ
#print axioms FNR.Memory.clone_cover
#audit_axioms_strict FNR.Memory.clone_cover
#print axioms FNR.Memory.blank_cover
#audit_axioms_strict FNR.Memory.blank_cover
#print axioms FNR.Memory.marked_of_markedFrom
#audit_axioms_strict FNR.Memory.marked_of_markedFrom
#print axioms FNR.Memory.dec_cloneCfg
#audit_axioms_strict FNR.Memory.dec_cloneCfg
#print axioms FNR.Memory.dec_blankCfg
#audit_axioms_strict FNR.Memory.dec_blankCfg
#print axioms FNR.Memory.dec_siteEquiv
#audit_axioms_strict FNR.Memory.dec_siteEquiv
#print axioms FNR.Memory.law_bad_le
#audit_axioms_strict FNR.Memory.law_bad_le
#print axioms FNR.Memory.memory_branch
#audit_axioms_strict FNR.Memory.memory_branch
#print axioms FNR.Avg.shift_shift
#audit_axioms_strict FNR.Avg.shift_shift
#print axioms FNR.Avg.map_shift_map_shift
#audit_axioms_strict FNR.Avg.map_shift_map_shift
#print axioms FNR.Avg.map_shift_zero
#audit_axioms_strict FNR.Avg.map_shift_zero
#print axioms FNR.Avg.isProbabilityMeasure_map_shift
#audit_axioms_strict FNR.Avg.isProbabilityMeasure_map_shift
#print axioms FNR.Avg.integral_map_shift
#audit_axioms_strict FNR.Avg.integral_map_shift
#print axioms FNR.Avg.isTI_of_unit
#audit_axioms_strict FNR.Avg.isTI_of_unit
#print axioms FNR.Avg.avg_le
#audit_axioms_strict FNR.Avg.avg_le
#print axioms FNR.Avg.avg_univ
#audit_axioms_strict FNR.Avg.avg_univ
#print axioms FNR.Avg.isProbabilityMeasure_savg
#audit_axioms_strict FNR.Avg.isProbabilityMeasure_savg
#print axioms FNR.Avg.integral_savg
#audit_axioms_strict FNR.Avg.integral_savg
#print axioms FNR.Avg.exists_savg_limit
#audit_axioms_strict FNR.Avg.exists_savg_limit
#print axioms FNR.Avg.abs_integral_savg_shift_le
#audit_axioms_strict FNR.Avg.abs_integral_savg_shift_le
#print axioms FNR.Avg.isInv_of_savg_limit
#audit_axioms_strict FNR.Avg.isInv_of_savg_limit
#print axioms FNR.Avg.savg_isInv
#audit_axioms_strict FNR.Avg.savg_isInv
#print axioms FNR.Avg.isInv_of_weakTendsto
#audit_axioms_strict FNR.Avg.isInv_of_weakTendsto
#print axioms FNR.Avg.isStationary_map_shift
#audit_axioms_strict FNR.Avg.isStationary_map_shift
#print axioms FNR.Avg.isStationary_savg
#audit_axioms_strict FNR.Avg.isStationary_savg
#print axioms FNR.Avg.isStationary_of_weakTendsto
#audit_axioms_strict FNR.Avg.isStationary_of_weakTendsto
#print axioms FNR.Avg.measurableSet_site
#audit_axioms_strict FNR.Avg.measurableSet_site
#print axioms FNR.Avg.savg_le
#audit_axioms_strict FNR.Avg.savg_le
#print axioms FNR.Avg.le_of_weakTendsto
#audit_axioms_strict FNR.Avg.le_of_weakTendsto
#print axioms FNR.Avg.exists_TI
#audit_axioms_strict FNR.Avg.exists_TI
#print axioms FNR.Avg.exists_stationary_le
#audit_axioms_strict FNR.Avg.exists_stationary_le
#print axioms FNR.Memory.clone_blank_le
#audit_axioms_strict FNR.Memory.clone_blank_le
#print axioms FNR.Memory.blank_live_le
#audit_axioms_strict FNR.Memory.blank_live_le
#print axioms FNR.Memory.twoTI_of_tiles
#audit_axioms_strict FNR.Memory.twoTI_of_tiles
#print axioms FNR.isPositiveRatePCA
#audit_axioms_strict FNR.isPositiveRatePCA
#print axioms FNR.theoremAFromDomino_of_classification
#audit_axioms_strict FNR.theoremAFromDomino_of_classification
#print axioms FNR.theoremAUndecidable_of_classification
#audit_axioms_strict FNR.theoremAUndecidable_of_classification
#print axioms FNR.tilesPlane_iff
#audit_axioms_strict FNR.tilesPlane_iff
#print axioms FNR.familyR_tiles_iff
#audit_axioms_strict FNR.familyR_tiles_iff
#print axioms FNR.domino_undecidable_of_reduction
#audit_axioms_strict FNR.domino_undecidable_of_reduction
#print axioms FNR.ergodicityUndecidable_of_reduction
#audit_axioms_strict FNR.ergodicityUndecidable_of_reduction
#print axioms FNR.machineCorollary_of_reduction
#audit_axioms_strict FNR.machineCorollary_of_reduction

/-! Complete imported audit, including generated and private declarations. -/
set_option maxHeartbeats 20000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut coreCount := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx]!
      let s := mod.toString
      let own := s.startsWith "ForgettingNaturalRule"
      let core := s.startsWith "FixedNoiseErgodicity" || s.startsWith "UndecidablePhaseDiagram" ||
        s.startsWith "UncomputableNoiseDiagram"
      if own || core then
        if ci matches .axiomInfo _ then throwError "Axiom declaration {n} in {mod}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        if own then
          logInfo m!"FNR_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          count := count + 1
        else
          logInfo m!"CORE_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          coreCount := coreCount + 1
  let check (n : Name) (t : Expr) : CommandElabM Unit := do
    let some ci := env.find? n | throwError "Missing {n}"
    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"
    unless ci.type == t do throwError "{n} statement changed"
  check ``FNR.natural_classification (mkConst ``FNR.NaturalClassification)
  check ``FNR.theorem_A (mkConst ``FNR.TheoremA)
  check ``FNR.machine_corollary (mkConst ``FNR.MachineCorollary)
  check ``FNR.domino_reduction (mkConst ``FNR.DominoReduction)
  check ``FNR.domino_undecidable (mkConst ``FNR.DominoUndecidable)
  logInfo m!"FNR_FINAL_TYPES_OK"
  check ``FNR.theorem_A_from_domino (mkConst ``FNR.TheoremAFromDomino)
  check ``FNR.theorem_A_undecidable (mkConst ``FNR.TheoremAUndecidable)
  logInfo m!"FNR_CONDITIONAL_TYPES_OK"
  logInfo m!"FNR_DECL_COUNT:{count}"
  logInfo m!"CORE_DECL_COUNT:{coreCount}"
