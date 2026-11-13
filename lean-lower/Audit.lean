/-
# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)

Prints and strictly audits every root of `ForgettingLower/Audit.lean` (the three release targets
first), then checks the axioms of every imported declaration of the development and of the imported
modules of the four reused cores (`FixedNoiseErgodicity.*`, `UndecidablePhaseDiagram.*`,
`UncomputableNoiseDiagram.*`, `ForgettingNaturalRule.*`), including private and generated ones: only `propext`, `Classical.choice`,
`Quot.sound` are allowed, and no such declaration is an axiom. Finally it checks the types of the three
release targets against their exact frozen types.
(Modelled on the noise-diagram, hard-model and forgetting relays' package `Audit.lean`.)
-/
import ForgettingLower
import UncomputableNoiseDiagram.AuditCommand

set_option autoImplicit false

#print axioms FLD.z4_classification
#audit_axioms_strict FLD.z4_classification
#print axioms FLD.z4_machine_corollary
#audit_axioms_strict FLD.z4_machine_corollary
#print axioms FLD.z4_raw_undecidable
#audit_axioms_strict FLD.z4_raw_undecidable
#print axioms FLD.Const.K_eq
#audit_axioms_strict FLD.Const.K_eq
#print axioms FLD.Const.q_eq
#audit_axioms_strict FLD.Const.q_eq
#print axioms FLD.Const.quorum_eq
#audit_axioms_strict FLD.Const.quorum_eq
#print axioms FLD.Const.Delta_eq
#audit_axioms_strict FLD.Const.Delta_eq
#print axioms FLD.Const.B_eq
#audit_axioms_strict FLD.Const.B_eq
#print axioms FLD.Const.delta_eq
#audit_axioms_strict FLD.Const.delta_eq
#print axioms FLD.Const.densityCost_eq
#audit_axioms_strict FLD.Const.densityCost_eq
#print axioms FLD.Const.eps0_pos
#audit_axioms_strict FLD.Const.eps0_pos
#print axioms FLD.Const.eps0_le_one
#audit_axioms_strict FLD.Const.eps0_le_one
#print axioms FLD.Const.eps0Rat_cast
#audit_axioms_strict FLD.Const.eps0Rat_cast
#print axioms FLD.Const.eps0_eq_B
#audit_axioms_strict FLD.Const.eps0_eq_B
#print axioms FLD.Const.densityCost_formula
#audit_axioms_strict FLD.Const.densityCost_formula
#print axioms FLD.Const.drift_margin
#audit_axioms_strict FLD.Const.drift_margin
#print axioms FLD.Density.exists_slab_selection
#audit_axioms_strict FLD.Density.exists_slab_selection
#print axioms FLD.Density.occurrence_card_le
#audit_axioms_strict FLD.Density.occurrence_card_le
#print axioms FLD.Density.occurrence_mass_le
#audit_axioms_strict FLD.Density.occurrence_mass_le
#print axioms FLD.Density.terminal_sets_pairwise_disjoint
#audit_axioms_strict FLD.Density.terminal_sets_pairwise_disjoint
#print axioms FLD.Density.terminal_union_card
#audit_axioms_strict FLD.Density.terminal_union_card
#print axioms FLD.Density.spur_contour_cost
#audit_axioms_strict FLD.Density.spur_contour_cost
#print axioms FLD.Density.whole_path_paid
#audit_axioms_strict FLD.Density.whole_path_paid
#print axioms FLD.Density.whole_union_paid
#audit_axioms_strict FLD.Density.whole_union_paid
#print axioms FLD.Density.interval_cost
#audit_axioms_strict FLD.Density.interval_cost
#print axioms FLD.Density.exists_density_accounting
#audit_axioms_strict FLD.Density.exists_density_accounting
#print axioms FLD.Density.encoding_sum_le
#audit_axioms_strict FLD.Density.encoding_sum_le
#print axioms FLD.common_neighbourhood
#audit_axioms_strict FLD.common_neighbourhood
#print axioms FLD.domino_reduction
#audit_axioms_strict FLD.domino_reduction
#print axioms FLD.Geometry.card_Provider
#audit_axioms_strict FLD.Geometry.card_Provider
#print axioms FLD.Geometry.chi_par
#audit_axioms_strict FLD.Geometry.chi_par
#print axioms FLD.Geometry.par_time
#audit_axioms_strict FLD.Geometry.par_time
#print axioms FLD.Geometry.par_ne
#audit_axioms_strict FLD.Geometry.par_ne
#print axioms FLD.Geometry.card_box_one
#audit_axioms_strict FLD.Geometry.card_box_one
#print axioms FLD.Geometry.card_nbr_le
#audit_axioms_strict FLD.Geometry.card_nbr_le
#print axioms FLD.Geometry.par_mem_nbr
#audit_axioms_strict FLD.Geometry.par_mem_nbr
#print axioms FLD.Geometry.mem_nbr_par
#audit_axioms_strict FLD.Geometry.mem_nbr_par
#print axioms FLD.Geometry.inGraph_par
#audit_axioms_strict FLD.Geometry.inGraph_par
#print axioms FLD.Geometry.not_isDiag_par
#audit_axioms_strict FLD.Geometry.not_isDiag_par
#print axioms FLD.Geometry.markedAt_mono
#audit_axioms_strict FLD.Geometry.markedAt_mono
#print axioms FLD.Geometry.twoCl_mono
#audit_axioms_strict FLD.Geometry.twoCl_mono
#print axioms FLD.Geometry.markedFrom_mono
#audit_axioms_strict FLD.Geometry.markedFrom_mono
#print axioms FLD.Geometry.markedFrom_mono'
#audit_axioms_strict FLD.Geometry.markedFrom_mono'
#print axioms FLD.Geometry.marked_closed
#audit_axioms_strict FLD.Geometry.marked_closed
#print axioms FLD.Geometry.markedFrom_le
#audit_axioms_strict FLD.Geometry.markedFrom_le
#print axioms FLD.Geometry.marked_le
#audit_axioms_strict FLD.Geometry.marked_le
#print axioms FLD.Geometry.marked_iff
#audit_axioms_strict FLD.Geometry.marked_iff
#print axioms FLD.Geometry.not_flag_of_not_marked
#audit_axioms_strict FLD.Geometry.not_flag_of_not_marked
#print axioms FLD.Geometry.one_cluster
#audit_axioms_strict FLD.Geometry.one_cluster
#print axioms FLD.Geometry.card_cluster
#audit_axioms_strict FLD.Geometry.card_cluster
#print axioms FLD.Geometry.card_marked_le
#audit_axioms_strict FLD.Geometry.card_marked_le
#print axioms FLD.Geometry.MF.time_lt
#audit_axioms_strict FLD.Geometry.MF.time_lt
#print axioms FLD.Geometry.mf_par
#audit_axioms_strict FLD.Geometry.mf_par
#print axioms FLD.Geometry.exists_pgood
#audit_axioms_strict FLD.Geometry.exists_pgood
#print axioms FLD.Geometry.pd_spec
#audit_axioms_strict FLD.Geometry.pd_spec
#print axioms FLD.Geometry.sel_box
#audit_axioms_strict FLD.Geometry.sel_box
#print axioms FLD.Geometry.sel_mf
#audit_axioms_strict FLD.Geometry.sel_mf
#print axioms FLD.Geometry.sel_ne
#audit_axioms_strict FLD.Geometry.sel_ne
#print axioms FLD.Geometry.sys_sup
#audit_axioms_strict FLD.Geometry.sys_sup
#print axioms FLD.Geometry.sel_good
#audit_axioms_strict FLD.Geometry.sel_good
#print axioms FLD.Geometry.psi_sum
#audit_axioms_strict FLD.Geometry.psi_sum
#print axioms FLD.Geometry.psi_par
#audit_axioms_strict FLD.Geometry.psi_par
#print axioms FLD.Geometry.isPotential_psi
#audit_axioms_strict FLD.Geometry.isPotential_psi
#print axioms FLD.Contour.gEdges_reach_end
#audit_axioms_strict FLD.Contour.gEdges_reach_end
#print axioms FLD.Contour.pEdges_reach_end
#audit_axioms_strict FLD.Contour.pEdges_reach_end
#print axioms FLD.Contour.witness_reach_end
#audit_axioms_strict FLD.Contour.witness_reach_end
#print axioms FLD.Contour.witness_terminal_bracket
#audit_axioms_strict FLD.Contour.witness_terminal_bracket
#print axioms FLD.Geometry.mf_of_reach
#audit_axioms_strict FLD.Geometry.mf_of_reach
#print axioms FLD.Geometry.flag_of_term
#audit_axioms_strict FLD.Geometry.flag_of_term
#print axioms FLD.Geometry.gLen_eq_gBin
#audit_axioms_strict FLD.Geometry.gLen_eq_gBin
#print axioms FLD.Geometry.armEdge_spec
#audit_axioms_strict FLD.Geometry.armEdge_spec
#print axioms FLD.Geometry.exists_edge_of_reach
#audit_axioms_strict FLD.Geometry.exists_edge_of_reach
#print axioms FLD.Geometry.isContour_flag
#audit_axioms_strict FLD.Geometry.isContour_flag
#print axioms FLD.Geometry.exists_contour_nf
#audit_axioms_strict FLD.Geometry.exists_contour_nf
#print axioms FLD.Geometry.exists_contour
#audit_axioms_strict FLD.Geometry.exists_contour
#print axioms FLD.Geometry.IsContour.edges_le
#audit_axioms_strict FLD.Geometry.IsContour.edges_le
#print axioms FLD.Geometry.IsContour.exists_earliest
#audit_axioms_strict FLD.Geometry.IsContour.exists_earliest
#print axioms FLD.Density.card_pathEdges_le
#audit_axioms_strict FLD.Density.card_pathEdges_le
#print axioms FLD.Density.pathEdges_reach
#audit_axioms_strict FLD.Density.pathEdges_reach
#print axioms FLD.Density.pathEdges_connected
#audit_axioms_strict FLD.Density.pathEdges_connected
#print axioms FLD.Density.pathEdges_inGraph
#audit_axioms_strict FLD.Density.pathEdges_inGraph
#print axioms FLD.Density.path_time
#audit_axioms_strict FLD.Density.path_time
#print axioms FLD.Density.exists_attachment
#audit_axioms_strict FLD.Density.exists_attachment
#print axioms FLD.Density.exists_density_encoding
#audit_axioms_strict FLD.Density.exists_density_encoding
#print axioms FLD.raw_undecidable_of_machine_corollary
#audit_axioms_strict FLD.raw_undecidable_of_machine_corollary
#print axioms FLD.Geometry.toSite_injective
#audit_axioms_strict FLD.Geometry.toSite_injective
#print axioms FLD.Geometry.noiseCoord_injective
#audit_axioms_strict FLD.Geometry.noiseCoord_injective
#print axioms FLD.Geometry.flags_measure
#audit_axioms_strict FLD.Geometry.flags_measure
#print axioms FLD.Density.minFlags_le_card
#audit_axioms_strict FLD.Density.minFlags_le_card
#print axioms FLD.Density.minFlags_pos
#audit_axioms_strict FLD.Density.minFlags_pos
#print axioms FLD.Density.densePathEv_encoding
#audit_axioms_strict FLD.Density.densePathEv_encoding
#print axioms FLD.Density.densePathEv_measure_le
#audit_axioms_strict FLD.Density.densePathEv_measure_le
#print axioms FLD.Const.density_base_le
#audit_axioms_strict FLD.Const.density_base_le
#print axioms FLD.Const.inv_densityCost_lt_quarter
#audit_axioms_strict FLD.Const.inv_densityCost_lt_quarter
#print axioms FLD.Const.density_base_lt_quarter
#audit_axioms_strict FLD.Const.density_base_lt_quarter
#print axioms FLD.Density.div_le_minFlags
#audit_axioms_strict FLD.Density.div_le_minFlags
#print axioms FLD.Density.tsum_pow_div_ne_top
#audit_axioms_strict FLD.Density.tsum_pow_div_ne_top
#print axioms FLD.Density.tsum_density_tail_ne_top
#audit_axioms_strict FLD.Density.tsum_density_tail_ne_top
#print axioms FLD.Density.tsum_densePathEv_ne_top
#audit_axioms_strict FLD.Density.tsum_densePathEv_ne_top
#print axioms FLD.Density.eventually_sparse_at
#audit_axioms_strict FLD.Density.eventually_sparse_at
#print axioms FLD.Density.all_path_density
#audit_axioms_strict FLD.Density.all_path_density
#print axioms FLD.Density.no_infinite_marked_paths
#audit_axioms_strict FLD.Density.no_infinite_marked_paths
#print axioms FLD.Density.raw_paths
#audit_axioms_strict FLD.Density.raw_paths
#print axioms FLD.Geometry.siteEquiv_site
#audit_axioms_strict FLD.Geometry.siteEquiv_site
#print axioms FLD.Geometry.siteEquiv_symm
#audit_axioms_strict FLD.Geometry.siteEquiv_symm
#print axioms FLD.Geometry.site_zero
#audit_axioms_strict FLD.Geometry.site_zero
#print axioms FLD.Geometry.symm_shift
#audit_axioms_strict FLD.Geometry.symm_shift
#print axioms FLD.Geometry.site_add
#audit_axioms_strict FLD.Geometry.site_add
#print axioms FLD.Rule.chkI_eq_some
#audit_axioms_strict FLD.Rule.chkI_eq_some
#print axioms FLD.Rule.mem_cardinal_zero
#audit_axioms_strict FLD.Rule.mem_cardinal_zero
#print axioms FLD.Rule.mem_cardinal_e1
#audit_axioms_strict FLD.Rule.mem_cardinal_e1
#print axioms FLD.Rule.mem_cardinal_w1
#audit_axioms_strict FLD.Rule.mem_cardinal_w1
#print axioms FLD.Rule.mem_cardinal_e2
#audit_axioms_strict FLD.Rule.mem_cardinal_e2
#print axioms FLD.Rule.mem_cardinal_w2
#audit_axioms_strict FLD.Rule.mem_cardinal_w2
#print axioms FLD.Rule.plane_add_zero
#audit_axioms_strict FLD.Rule.plane_add_zero
#print axioms FLD.Rule.cardinal_sub_box
#audit_axioms_strict FLD.Rule.cardinal_sub_box
#print axioms FLD.Rule.chkI_congr
#audit_axioms_strict FLD.Rule.chkI_congr
#print axioms FLD.Rule.quorum_unique
#audit_axioms_strict FLD.Rule.quorum_unique
#print axioms FLD.Rule.GI_eq_some_iff
#audit_axioms_strict FLD.Rule.GI_eq_some_iff
#print axioms FLD.Rule.card_failed_le
#audit_axioms_strict FLD.Rule.card_failed_le
#print axioms FLD.Rule.GI_congr
#audit_axioms_strict FLD.Rule.GI_congr
#print axioms FLD.Rule.disc_parent
#audit_axioms_strict FLD.Rule.disc_parent
#print axioms FLD.Rule.chkI_clone_inputs
#audit_axioms_strict FLD.Rule.chkI_clone_inputs
#print axioms FLD.Rule.GI_live_centres
#audit_axioms_strict FLD.Rule.GI_live_centres
#print axioms FLD.Rule.card_bad_of_ne_clone
#audit_axioms_strict FLD.Rule.card_bad_of_ne_clone
#print axioms FLD.Rule.twoCl_of_card
#audit_axioms_strict FLD.Rule.twoCl_of_card
#print axioms FLD.Rule.check_translate
#audit_axioms_strict FLD.Rule.check_translate
#print axioms FLD.Rule.natMap_translate
#audit_axioms_strict FLD.Rule.natMap_translate
#print axioms FLD.Rule.natMap_eq
#audit_axioms_strict FLD.Rule.natMap_eq
#print axioms FLD.Rule.natMap_local
#audit_axioms_strict FLD.Rule.natMap_local
#print axioms FLD.Rule.natCA_apply
#audit_axioms_strict FLD.Rule.natCA_apply
#print axioms FLD.Rule.dec_update
#audit_axioms_strict FLD.Rule.dec_update
#print axioms FLD.Rule.dec_inj
#audit_axioms_strict FLD.Rule.dec_inj
#print axioms FLD.Rule.isTraj_of_complete
#audit_axioms_strict FLD.Rule.isTraj_of_complete
#print axioms FLD.Rule.complete_flag_eq
#audit_axioms_strict FLD.Rule.complete_flag_eq
#print axioms FLD.Rule.isTraj_flow
#audit_axioms_strict FLD.Rule.isTraj_flow
#print axioms FLD.Rule.flowTraj_zero
#audit_axioms_strict FLD.Rule.flowTraj_zero
#print axioms FLD.Rule.flowTraj_nat
#audit_axioms_strict FLD.Rule.flowTraj_nat
#print axioms FLD.Coh.UL.gi
#audit_axioms_strict FLD.Coh.UL.gi
#print axioms FLD.Coh.keepsI_live
#audit_axioms_strict FLD.Coh.keepsI_live
#print axioms FLD.Coh.ul_of_good
#audit_axioms_strict FLD.Coh.ul_of_good
#print axioms FLD.Coh.ul_nbr_of_good
#audit_axioms_strict FLD.Coh.ul_nbr_of_good
#print axioms FLD.Coh.IsHistory.isTraj
#audit_axioms_strict FLD.Coh.IsHistory.isTraj
#print axioms FLD.Coh.isHistory_of_complete
#audit_axioms_strict FLD.Coh.isHistory_of_complete
#print axioms FLD.Coh.card_good_ge
#audit_axioms_strict FLD.Coh.card_good_ge
#print axioms FLD.Coh.exists_good
#audit_axioms_strict FLD.Coh.exists_good
#print axioms FLD.Coh.clean_of_not_H
#audit_axioms_strict FLD.Coh.clean_of_not_H
#print axioms FLD.Coh.coh_back
#audit_axioms_strict FLD.Coh.coh_back
#print axioms FLD.Coh.card_PSrc
#audit_axioms_strict FLD.Coh.card_PSrc
#print axioms FLD.Coh.insertNth_inj
#audit_axioms_strict FLD.Coh.insertNth_inj
#print axioms FLD.Coh.pHi_injective
#audit_axioms_strict FLD.Coh.pHi_injective
#print axioms FLD.Coh.pLo_injective
#audit_axioms_strict FLD.Coh.pLo_injective
#print axioms FLD.Coh.offset_pair
#audit_axioms_strict FLD.Coh.offset_pair
#print axioms FLD.Coh.exists_pair
#audit_axioms_strict FLD.Coh.exists_pair
#print axioms FLD.Coh.sep_zero
#audit_axioms_strict FLD.Coh.sep_zero
#print axioms FLD.Coh.sep_step
#audit_axioms_strict FLD.Coh.sep_step
#print axioms FLD.Coh.offset_bounds
#audit_axioms_strict FLD.Coh.offset_bounds
#print axioms FLD.Coh.sep_offset_le
#audit_axioms_strict FLD.Coh.sep_offset_le
#print axioms FLD.Coh.sep_add_le
#audit_axioms_strict FLD.Coh.sep_add_le
#print axioms FLD.Coh.transverse_ne
#audit_axioms_strict FLD.Coh.transverse_ne
#print axioms FLD.Coh.paired_step
#audit_axioms_strict FLD.Coh.paired_step
#print axioms FLD.Coh.distance_drift
#audit_axioms_strict FLD.Coh.distance_drift
#print axioms FLD.Coh.same_site
#audit_axioms_strict FLD.Coh.same_site
#print axioms FLD.Coh.same_site_ae
#audit_axioms_strict FLD.Coh.same_site_ae
#print axioms FLD.Coh.east_edge
#audit_axioms_strict FLD.Coh.east_edge
#print axioms FLD.Coh.north_edge
#audit_axioms_strict FLD.Coh.north_edge
#print axioms FLD.Coh.west_edge
#audit_axioms_strict FLD.Coh.west_edge
#print axioms FLD.Coh.south_edge
#audit_axioms_strict FLD.Coh.south_edge
#print axioms FLD.Coh.edge_matching_ae
#audit_axioms_strict FLD.Coh.edge_matching_ae
#print axioms FLD.Coh.ul_down
#audit_axioms_strict FLD.Coh.ul_down
#print axioms FLD.Coh.ul_move
#audit_axioms_strict FLD.Coh.ul_move
#print axioms FLD.Coh.add_pair
#audit_axioms_strict FLD.Coh.add_pair
#print axioms FLD.Coh.ul_reach
#audit_axioms_strict FLD.Coh.ul_reach
#print axioms FLD.Coh.ul_common
#audit_axioms_strict FLD.Coh.ul_common
#print axioms FLD.Coh.ul_same
#audit_axioms_strict FLD.Coh.ul_same
#print axioms FLD.Coh.ul_east
#audit_axioms_strict FLD.Coh.ul_east
#print axioms FLD.Coh.ul_north
#audit_axioms_strict FLD.Coh.ul_north
#print axioms FLD.Coh.tiles_of_UL
#audit_axioms_strict FLD.Coh.tiles_of_UL
#print axioms FLD.Coh.live_marked
#audit_axioms_strict FLD.Coh.live_marked
#print axioms FLD.Coh.extraction_ae
#audit_axioms_strict FLD.Coh.extraction_ae
#print axioms FLD.Forget.disc_step
#audit_axioms_strict FLD.Forget.disc_step
#print axioms FLD.Forget.disc_path
#audit_axioms_strict FLD.Forget.disc_path
#print axioms FLD.Forget.unique_complete_all
#audit_axioms_strict FLD.Forget.unique_complete_all
#print axioms FLD.Forget.unique_complete
#audit_axioms_strict FLD.Forget.unique_complete
#print axioms FLD.Forget.ergodic_of_not_tiles
#audit_axioms_strict FLD.Forget.ergodic_of_not_tiles
#print axioms FLD.Forget.flow_timeNoise
#audit_axioms_strict FLD.Forget.flow_timeNoise
#print axioms FLD.Forget.complete_timeNoise
#audit_axioms_strict FLD.Forget.complete_timeNoise
#print axioms FLD.Forget.all_time_singleton
#audit_axioms_strict FLD.Forget.all_time_singleton
#print axioms FLD.Forget.allTimeCFTP_of_not_tiles
#audit_axioms_strict FLD.Forget.allTimeCFTP_of_not_tiles
#print axioms FLD.Memory.traj_succ
#audit_axioms_strict FLD.Memory.traj_succ
#print axioms FLD.Memory.clone_cover
#audit_axioms_strict FLD.Memory.clone_cover
#print axioms FLD.Memory.blank_cover
#audit_axioms_strict FLD.Memory.blank_cover
#print axioms FLD.Memory.marked_of_markedFrom
#audit_axioms_strict FLD.Memory.marked_of_markedFrom
#print axioms FLD.Forget.root_encoding
#audit_axioms_strict FLD.Forget.root_encoding
#print axioms FLD.Forget.root_measure_le
#audit_axioms_strict FLD.Forget.root_measure_le
#print axioms FLD.Forget.root_base_le
#audit_axioms_strict FLD.Forget.root_base_le
#print axioms FLD.Forget.root_tail_le
#audit_axioms_strict FLD.Forget.root_tail_le
#print axioms FLD.Forget.root_bound
#audit_axioms_strict FLD.Forget.root_bound
#print axioms FLD.Memory.dec_cloneCfg
#audit_axioms_strict FLD.Memory.dec_cloneCfg
#print axioms FLD.Memory.dec_blankCfg
#audit_axioms_strict FLD.Memory.dec_blankCfg
#print axioms FLD.Memory.dec_siteEquiv
#audit_axioms_strict FLD.Memory.dec_siteEquiv
#print axioms FLD.Memory.law_bad_le
#audit_axioms_strict FLD.Memory.law_bad_le
#print axioms FLD.Memory.memory_branch
#audit_axioms_strict FLD.Memory.memory_branch
#print axioms FLD.Memory.clone_blank_le
#audit_axioms_strict FLD.Memory.clone_blank_le
#print axioms FLD.Memory.blank_live_le
#audit_axioms_strict FLD.Memory.blank_live_le
#print axioms FLD.Memory.twoInvariant_of_tiles
#audit_axioms_strict FLD.Memory.twoInvariant_of_tiles

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
      let own := s.startsWith "ForgettingLower"
      let core := s.startsWith "FixedNoiseErgodicity" || s.startsWith "UndecidablePhaseDiagram" ||
        s.startsWith "UncomputableNoiseDiagram" || s.startsWith "ForgettingNaturalRule"
      if own || core then
        if ci matches .axiomInfo _ then throwError "Axiom declaration {n} in {mod}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        if own then
          logInfo m!"FLD_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          count := count + 1
        else
          logInfo m!"CORE_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          coreCount := coreCount + 1
  let check (n : Name) (t : Expr) : CommandElabM Unit := do
    let some ci := env.find? n | throwError "Missing {n}"
    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"
    unless ci.type == t do throwError "{n} statement changed"
  check ``FLD.z4_classification (mkConst ``FLD.Z4Classification)
  check ``FLD.z4_machine_corollary (mkConst ``FLD.Z4MachineCorollary)
  check ``FLD.z4_raw_undecidable (mkConst ``FLD.Z4RawUndecidable)
  logInfo m!"FLD_FINAL_TYPES_OK"
  logInfo m!"FLD_DECL_COUNT:{count}"
  logInfo m!"CORE_DECL_COUNT:{coreCount}"
