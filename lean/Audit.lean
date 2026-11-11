import FixedNoiseErgodicity

set_option autoImplicit false

#print axioms FNE.cor_eight
#audit_axioms_strict FNE.cor_eight
#print axioms FNE.cor_eight_undecidable_statement
#audit_axioms_strict FNE.cor_eight_undecidable_statement
#print axioms FNE.cor_eight_undecidable
#audit_axioms_strict FNE.cor_eight_undecidable
#print axioms FNE.nonergodic_not_re
#audit_axioms_strict FNE.nonergodic_not_re
#print axioms FNE.halts_not_computable
#audit_axioms_strict FNE.halts_not_computable
#print axioms FNE.not_halts_not_re
#audit_axioms_strict FNE.not_halts_not_re
#print axioms FNE.eps0_eq
#audit_axioms_strict FNE.eps0_eq
#print axioms FNE.quorum_unique
#audit_axioms_strict FNE.quorum_unique
#print axioms FNE.quorumRule_eq_live_iff
#audit_axioms_strict FNE.quorumRule_eq_live_iff
#print axioms FNE.quorumRule_eq_bot_iff
#audit_axioms_strict FNE.quorumRule_eq_bot_iff
#print axioms FNE.TokenGame.refutable_iff_not_exists_planeSafe
#audit_axioms_strict FNE.TokenGame.refutable_iff_not_exists_planeSafe
#print axioms FNE.TokenGame.not_refutable_of_tiles
#audit_axioms_strict FNE.TokenGame.not_refutable_of_tiles
#print axioms FNE.TokenGame.walk
#audit_axioms_strict FNE.TokenGame.walk
#print axioms FNE.TokenGame.safe_subset_tables
#audit_axioms_strict FNE.TokenGame.safe_subset_tables
#print axioms FNE.TokenGame.limitTable_safe
#audit_axioms_strict FNE.TokenGame.limitTable_safe
#print axioms FNE.checkAll_eq_cloned
#audit_axioms_strict FNE.checkAll_eq_cloned
#print axioms FNE.quorumRule_cloned
#audit_axioms_strict FNE.quorumRule_cloned
#print axioms FNE.providers_of_live
#audit_axioms_strict FNE.providers_of_live
#print axioms FNE.two_bad_parents_cloned
#audit_axioms_strict FNE.two_bad_parents_cloned
#print axioms FNE.two_bad_parents_bot
#audit_axioms_strict FNE.two_bad_parents_bot
#print axioms FNE.dominate_cloned
#audit_axioms_strict FNE.dominate_cloned
#print axioms FNE.dominate_bot
#audit_axioms_strict FNE.dominate_bot
#print axioms FNE.EdgeCount.exists_covering_walk
#audit_axioms_strict FNE.EdgeCount.exists_covering_walk
#print axioms FNE.EdgeCount.card_le_pow
#audit_axioms_strict FNE.EdgeCount.card_le_pow
#print axioms FNE.mem_inst_of_family
#audit_axioms_strict FNE.mem_inst_of_family
#print axioms FNE.presentFamily_closed
#audit_axioms_strict FNE.presentFamily_closed
#print axioms FNE.transport
#audit_axioms_strict FNE.transport
#print axioms FNE.cover
#audit_axioms_strict FNE.cover
#print axioms FNE.live_marked
#audit_axioms_strict FNE.live_marked
#print axioms FNE.gCount
#audit_axioms_strict FNE.gCount
#print axioms FNE.gCount_D0
#audit_axioms_strict FNE.gCount_D0
#print axioms FNE.finite_connected
#audit_axioms_strict FNE.finite_connected
#print axioms FNE.Contour.SupportSystem.exists_bij
#audit_axioms_strict FNE.Contour.SupportSystem.exists_bij
#print axioms FNE.Contour.SupportSystem.contour
#audit_axioms_strict FNE.Contour.SupportSystem.contour
#print axioms FNE.psiG_sum
#audit_axioms_strict FNE.psiG_sum
#print axioms FNE.psiG_step
#audit_axioms_strict FNE.psiG_step
#print axioms FNE.contourG
#audit_axioms_strict FNE.contourG
#print axioms FNE.contour_marked
#audit_axioms_strict FNE.contour_marked
#print axioms FNE.isProbabilityMeasure_noiseLaw
#audit_axioms_strict FNE.isProbabilityMeasure_noiseLaw
#print axioms FNE.quorumRule_local
#audit_axioms_strict FNE.quorumRule_local
#print axioms FNE.measurable_run
#audit_axioms_strict FNE.measurable_run
#print axioms FNE.isProbabilityMeasure_law
#audit_axioms_strict FNE.isProbabilityMeasure_law
#print axioms FNE.law_zero
#audit_axioms_strict FNE.law_zero
#print axioms FNE.law_apply_eq_lintegral
#audit_axioms_strict FNE.law_apply_eq_lintegral
#print axioms FNE.noiseLaw_flags_eq
#audit_axioms_strict FNE.noiseLaw_flags_eq
#print axioms FNE.noiseLaw_map_splitN
#audit_axioms_strict FNE.noiseLaw_map_splitN
#print axioms FNE.law_dirac_one
#audit_axioms_strict FNE.law_dirac_one
#print axioms FNE.law_succ'
#audit_axioms_strict FNE.law_succ'
#print axioms FNE.law_succ
#audit_axioms_strict FNE.law_succ
#print axioms FNE.siteLaw_pos
#audit_axioms_strict FNE.siteLaw_pos
#print axioms FNE.not_ergodic_of_memory
#audit_axioms_strict FNE.not_ergodic_of_memory
#print axioms FNE.EdgeCount.exists_vertices
#audit_axioms_strict FNE.EdgeCount.exists_vertices
#print axioms FNE.eps0_eq_epsK
#audit_axioms_strict FNE.eps0_eq_epsK
#print axioms FNE.beta_le_half
#audit_axioms_strict FNE.beta_le_half
#print axioms FNE.lam_le
#audit_axioms_strict FNE.lam_le
#print axioms FNE.memoryBound_lt
#audit_axioms_strict FNE.memoryBound_lt
#print axioms FNE.noiseLaw_allEvents_le
#audit_axioms_strict FNE.noiseLaw_allEvents_le
#print axioms FNE.peierls
#audit_axioms_strict FNE.peierls
#print axioms FNE.field_bound
#audit_axioms_strict FNE.field_bound
#print axioms FNE.memory
#audit_axioms_strict FNE.memory
#print axioms FNE.hasMemory_of_tiling
#audit_axioms_strict FNE.hasMemory_of_tiling
#print axioms FNE.not_ergodic_of_tiles
#audit_axioms_strict FNE.not_ergodic_of_tiles
#print axioms FNE.discrepancy_path
#audit_axioms_strict FNE.discrepancy_path
#print axioms FNE.slabs
#audit_axioms_strict FNE.slabs
#print axioms FNE.packing
#audit_axioms_strict FNE.packing
#print axioms FNE.forgetting
#audit_axioms_strict FNE.forgetting
#print axioms FNE.forgetting_tv
#audit_axioms_strict FNE.forgetting_tv
#print axioms FNE.forgets_of_refutable
#audit_axioms_strict FNE.forgets_of_refutable
#print axioms FNE.continuous_run
#audit_axioms_strict FNE.continuous_run
#print axioms FNE.integral_law
#audit_axioms_strict FNE.integral_law
#print axioms FNE.continuous_Phi
#audit_axioms_strict FNE.continuous_Phi
#print axioms FNE.isInvariant_of_cesaro_limit
#audit_axioms_strict FNE.isInvariant_of_cesaro_limit
#print axioms FNE.exists_cesaro_limit
#audit_axioms_strict FNE.exists_cesaro_limit
#print axioms FNE.exists_invariant
#audit_axioms_strict FNE.exists_invariant
#print axioms FNE.exists_window_approx
#audit_axioms_strict FNE.exists_window_approx
#print axioms FNE.weakTendsto_of_cyl
#audit_axioms_strict FNE.weakTendsto_of_cyl
#print axioms FNE.weakTendsto_iff_cyl
#audit_axioms_strict FNE.weakTendsto_iff_cyl
#print axioms FNE.weakTendsto_iff_dtv
#audit_axioms_strict FNE.weakTendsto_iff_dtv
#print axioms FNE.law_toReal_eq_integral
#audit_axioms_strict FNE.law_toReal_eq_integral
#print axioms FNE.dtv_law_le
#audit_axioms_strict FNE.dtv_law_le
#print axioms FNE.ergodic_of_forgets
#audit_axioms_strict FNE.ergodic_of_forgets
#print axioms FNE.two_invariant_of_memory
#audit_axioms_strict FNE.two_invariant_of_memory
#print axioms FNE.quorumRule_translate
#audit_axioms_strict FNE.quorumRule_translate
#print axioms FNE.isPositiveRatePCA
#audit_axioms_strict FNE.isPositiveRatePCA
#print axioms FNE.ergodic_of_refutable
#audit_axioms_strict FNE.ergodic_of_refutable
#print axioms FNE.theoremB
#audit_axioms_strict FNE.theoremB
#print axioms FNE.eight_of_dichotomy
#audit_axioms_strict FNE.eight_of_dichotomy
#print axioms FNE.cor_eight_of_theoremC
#audit_axioms_strict FNE.cor_eight_of_theoremC
#print axioms FNE.isTiling_iff_isLegalPattern
#audit_axioms_strict FNE.isTiling_iff_isLegalPattern
#print axioms FNE.tiles_of_forall_box
#audit_axioms_strict FNE.tiles_of_forall_box
#print axioms FNE.tiles_of_forall_square
#audit_axioms_strict FNE.tiles_of_forall_square
#print axioms FNE.compact
#audit_axioms_strict FNE.compact
#print axioms FNE.Scaffold.F_epN
#audit_axioms_strict FNE.Scaffold.F_epN
#print axioms FNE.Scaffold.F_epS
#audit_axioms_strict FNE.Scaffold.F_epS
#print axioms FNE.Scaffold.F_epE
#audit_axioms_strict FNE.Scaffold.F_epE
#print axioms FNE.Scaffold.F_epW
#audit_axioms_strict FNE.Scaffold.F_epW
#print axioms FNE.Scaffold.F_injective
#audit_axioms_strict FNE.Scaffold.F_injective
#print axioms FNE.Scaffold.thin_matchE_iff
#audit_axioms_strict FNE.Scaffold.thin_matchE_iff
#print axioms FNE.Scaffold.thin_matchN_iff
#audit_axioms_strict FNE.Scaffold.thin_matchN_iff
#print axioms FNE.Scaffold.se_spec
#audit_axioms_strict FNE.Scaffold.se_spec
#print axioms FNE.Scaffold.se_unique
#audit_axioms_strict FNE.Scaffold.se_unique
#print axioms FNE.Scaffold.nw_spec
#audit_axioms_strict FNE.Scaffold.nw_spec
#print axioms FNE.Scaffold.nw_unique
#audit_axioms_strict FNE.Scaffold.nw_unique
#print axioms FNE.Scaffold.Formal.baseList_length
#audit_axioms_strict FNE.Scaffold.Formal.baseList_length
#print axioms FNE.Scaffold.Formal.tab_alphabet_rows
#audit_axioms_strict FNE.Scaffold.Formal.tab_alphabet_rows
#print axioms FNE.Scaffold.Formal.InO.corner
#audit_axioms_strict FNE.Scaffold.Formal.InO.corner
#print axioms FNE.Scaffold.Formal.col_injective
#audit_axioms_strict FNE.Scaffold.Formal.col_injective
#print axioms FNE.Scaffold.Letter.letters_length
#audit_axioms_strict FNE.Scaffold.Letter.letters_length
#print axioms FNE.Scaffold.Letter.letters_nodup
#audit_axioms_strict FNE.Scaffold.Letter.letters_nodup
#print axioms FNE.Scaffold.Letter.tab_letters_rows
#audit_axioms_strict FNE.Scaffold.Letter.tab_letters_rows
#print axioms FNE.Scaffold.Letter.col_injective
#audit_axioms_strict FNE.Scaffold.Letter.col_injective
#print axioms FNE.Scaffold.Letter.MatchN.b1_eq
#audit_axioms_strict FNE.Scaffold.Letter.MatchN.b1_eq
#print axioms FNE.Scaffold.Letter.MatchE.b2_eq
#audit_axioms_strict FNE.Scaffold.Letter.MatchE.b2_eq
#print axioms FNE.Scaffold.legalOn_subst2_iff
#audit_axioms_strict FNE.Scaffold.legalOn_subst2_iff
#print axioms FNE.Scaffold.Formal.InO.child
#audit_axioms_strict FNE.Scaffold.Formal.InO.child
#print axioms FNE.Scaffold.Formal.phi_legal
#audit_axioms_strict FNE.Scaffold.Formal.phi_legal
#print axioms FNE.Scaffold.Formal.legalOn_phi_iff
#audit_axioms_strict FNE.Scaffold.Formal.legalOn_phi_iff
#print axioms FNE.Scaffold.Formal.child_injective
#audit_axioms_strict FNE.Scaffold.Formal.child_injective
#print axioms FNE.Scaffold.Letter.InA.child
#audit_axioms_strict FNE.Scaffold.Letter.InA.child
#print axioms FNE.Scaffold.Letter.phi'_legal
#audit_axioms_strict FNE.Scaffold.Letter.phi'_legal
#print axioms FNE.Scaffold.Letter.legalOn_phi'_iff
#audit_axioms_strict FNE.Scaffold.Letter.legalOn_phi'_iff
#print axioms FNE.Scaffold.Letter.child_injective
#audit_axioms_strict FNE.Scaffold.Letter.child_injective
#print axioms FNE.Scaffold.phi'_iterate_two_mul
#audit_axioms_strict FNE.Scaffold.phi'_iterate_two_mul
#print axioms FNE.Scaffold.legalOn_sigma_iff
#audit_axioms_strict FNE.Scaffold.legalOn_sigma_iff
#print axioms FNE.Scaffold.sigmaPow_legal
#audit_axioms_strict FNE.Scaffold.sigmaPow_legal
#print axioms FNE.Scaffold.sigma_injective
#audit_axioms_strict FNE.Scaffold.sigma_injective
#print axioms FNE.Scaffold.sigma_bits
#audit_axioms_strict FNE.Scaffold.sigma_bits
#print axioms FNE.Scaffold.iterate_sigmaPat_block
#audit_axioms_strict FNE.Scaffold.iterate_sigmaPat_block
#print axioms FNE.Scaffold.sigmaPow_succ_apply
#audit_axioms_strict FNE.Scaffold.sigmaPow_succ_apply
#print axioms FNE.Scaffold.Letter.toTile_injective
#audit_axioms_strict FNE.Scaffold.Letter.toTile_injective
#print axioms FNE.Scaffold.card_scaffoldSet
#audit_axioms_strict FNE.Scaffold.card_scaffoldSet
#print axioms FNE.Scaffold.scaffold_tiles
#audit_axioms_strict FNE.Scaffold.scaffold_tiles
#print axioms FNE.Scaffold.exists_letter_tiling
#audit_axioms_strict FNE.Scaffold.exists_letter_tiling
#print axioms FNE.Scaffold.fit_pairs_count
#audit_axioms_strict FNE.Scaffold.fit_pairs_count
#print axioms FNE.Scaffold.Thin.epE_eq_epW_iff
#audit_axioms_strict FNE.Scaffold.Thin.epE_eq_epW_iff
#print axioms FNE.Scaffold.Thin.epN_eq_epS_iff
#audit_axioms_strict FNE.Scaffold.Thin.epN_eq_epS_iff
#print axioms FNE.Scaffold.Thin.F_epE_eq_F_epW_iff
#audit_axioms_strict FNE.Scaffold.Thin.F_epE_eq_F_epW_iff
#print axioms FNE.Scaffold.Thin.F_epN_eq_F_epS_iff
#audit_axioms_strict FNE.Scaffold.Thin.F_epN_eq_F_epS_iff
#print axioms FNE.Scaffold.Thin.four_distinct
#audit_axioms_strict FNE.Scaffold.Thin.four_distinct
#print axioms FNE.Scaffold.Letter.InA.cornerLetter
#audit_axioms_strict FNE.Scaffold.Letter.InA.cornerLetter
#print axioms FNE.Scaffold.Letter.InA.thin_b
#audit_axioms_strict FNE.Scaffold.Letter.InA.thin_b
#print axioms FNE.Scaffold.T1
#audit_axioms_strict FNE.Scaffold.T1
#print axioms FNE.Scaffold.T2
#audit_axioms_strict FNE.Scaffold.T2
#print axioms FNE.Scaffold.T3_c
#audit_axioms_strict FNE.Scaffold.T3_c
#print axioms FNE.Scaffold.T3_d
#audit_axioms_strict FNE.Scaffold.T3_d
#print axioms FNE.Scaffold.T3_bits
#audit_axioms_strict FNE.Scaffold.T3_bits
#print axioms FNE.Scaffold.T4
#audit_axioms_strict FNE.Scaffold.T4
#print axioms FNE.Scaffold.T5_black
#audit_axioms_strict FNE.Scaffold.T5_black
#print axioms FNE.Scaffold.T5_letter
#audit_axioms_strict FNE.Scaffold.T5_letter
#print axioms FNE.Scaffold.corner_red_endpoints
#audit_axioms_strict FNE.Scaffold.corner_red_endpoints
#print axioms FNE.Scaffold.letterAt_inA
#audit_axioms_strict FNE.Scaffold.letterAt_inA
#print axioms FNE.Scaffold.exists_letterAt
#audit_axioms_strict FNE.Scaffold.exists_letterAt
#print axioms FNE.Scaffold.letterAt_injective
#audit_axioms_strict FNE.Scaffold.letterAt_injective
#print axioms FNE.Scaffold.Letter.fits_iff
#audit_axioms_strict FNE.Scaffold.Letter.fits_iff
#print axioms FNE.Scaffold.fitCode_iff
#audit_axioms_strict FNE.Scaffold.fitCode_iff
#print axioms FNE.Scaffold.testBit_listMask
#audit_axioms_strict FNE.Scaffold.testBit_listMask
#print axioms FNE.Scaffold.testBit_letterMask
#audit_axioms_strict FNE.Scaffold.testBit_letterMask
#print axioms FNE.Scaffold.letterMask_eq_zero_iff
#audit_axioms_strict FNE.Scaffold.letterMask_eq_zero_iff
#print axioms FNE.Scaffold.testBit_fitMask
#audit_axioms_strict FNE.Scaffold.testBit_fitMask
#print axioms FNE.Family.eq_digits
#audit_axioms_strict FNE.Family.eq_digits
#print axioms FNE.Family.emod_eq_wsum_dig
#audit_axioms_strict FNE.Family.emod_eq_wsum_dig
#print axioms FNE.Family.IsRank.emod
#audit_axioms_strict FNE.Family.IsRank.emod
#print axioms FNE.Family.isRank_of_emod
#audit_axioms_strict FNE.Family.isRank_of_emod
#print axioms FNE.Family.IsLetterTiling.sub
#audit_axioms_strict FNE.Family.IsLetterTiling.sub
#print axioms FNE.Family.exists_tower
#audit_axioms_strict FNE.Family.exists_tower
#print axioms FNE.Family.TowerRel.chain
#audit_axioms_strict FNE.Family.TowerRel.chain
#print axioms FNE.Family.rank_bits_col
#audit_axioms_strict FNE.Family.rank_bits_col
#print axioms FNE.Family.rank_bits_row
#audit_axioms_strict FNE.Family.rank_bits_row
#print axioms FNE.Family.red_chain_col
#audit_axioms_strict FNE.Family.red_chain_col
#print axioms FNE.Family.red_chain_row
#audit_axioms_strict FNE.Family.red_chain_row
#print axioms FNE.Family.red_col
#audit_axioms_strict FNE.Family.red_col
#print axioms FNE.Family.red_row
#audit_axioms_strict FNE.Family.red_row
#print axioms FNE.Family.SPair.matchE_iff
#audit_axioms_strict FNE.Family.SPair.matchE_iff
#print axioms FNE.Family.SPair.matchN_iff
#audit_axioms_strict FNE.Family.SPair.matchN_iff
#print axioms FNE.Family.legalOn_quarter_iff
#audit_axioms_strict FNE.Family.legalOn_quarter_iff
#print axioms FNE.Family.IsLetterTiling.quarter
#audit_axioms_strict FNE.Family.IsLetterTiling.quarter
#print axioms FNE.Family.inFrame_iff
#audit_axioms_strict FNE.Family.inFrame_iff
#print axioms FNE.Family.isLeftEnd_iff
#audit_axioms_strict FNE.Family.isLeftEnd_iff
#print axioms FNE.Family.isRightEnd_iff
#audit_axioms_strict FNE.Family.isRightEnd_iff
#print axioms FNE.Family.rank_of_endpoint
#audit_axioms_strict FNE.Family.rank_of_endpoint
#print axioms FNE.Family.walls_col
#audit_axioms_strict FNE.Family.walls_col
#print axioms FNE.Family.walls_row
#audit_axioms_strict FNE.Family.walls_row
#print axioms FNE.Family.FrameOffsets.emod
#audit_axioms_strict FNE.Family.FrameOffsets.emod
#print axioms FNE.Family.frameOffsets_tower
#audit_axioms_strict FNE.Family.frameOffsets_tower
#print axioms FNE.Family.frame_window_unique
#audit_axioms_strict FNE.Family.frame_window_unique
#print axioms FNE.Family.endpoint_not_inFrame
#audit_axioms_strict FNE.Family.endpoint_not_inFrame
#print axioms FNE.Family.frames_nested
#audit_axioms_strict FNE.Family.frames_nested
#print axioms FNE.Family.frames_contain
#audit_axioms_strict FNE.Family.frames_contain
#print axioms FNE.Family.Laminar.endpoint_unique
#audit_axioms_strict FNE.Family.Laminar.endpoint_unique
#print axioms FNE.Family.Laminar.mem_of_consecutive
#audit_axioms_strict FNE.Family.Laminar.mem_of_consecutive
#print axioms FNE.Family.Laminar.consecutive_of_minimal
#audit_axioms_strict FNE.Family.Laminar.consecutive_of_minimal
#print axioms FNE.Family.three_wsum_third
#audit_axioms_strict FNE.Family.three_wsum_third
#print axioms FNE.Family.three_wsum_third_emod
#audit_axioms_strict FNE.Family.three_wsum_third_emod
#print axioms FNE.Family.three_towerOffsets_third
#audit_axioms_strict FNE.Family.three_towerOffsets_third
#print axioms FNE.Family.exists_interior_third
#audit_axioms_strict FNE.Family.exists_interior_third
#print axioms FNE.Family.exists_rank_third
#audit_axioms_strict FNE.Family.exists_rank_third
#print axioms FNE.Family.own_spec
#audit_axioms_strict FNE.Family.own_spec
#print axioms FNE.Family.not_carrier_of_wall
#audit_axioms_strict FNE.Family.not_carrier_of_wall
#print axioms FNE.Family.routing
#audit_axioms_strict FNE.Family.routing
#print axioms FNE.Family.lineFlow_rules
#audit_axioms_strict FNE.Family.lineFlow_rules
#print axioms FNE.Family.rowWall_iff
#audit_axioms_strict FNE.Family.rowWall_iff
#print axioms FNE.Family.colWall_iff
#audit_axioms_strict FNE.Family.colWall_iff
#print axioms FNE.Family.positive_a
#audit_axioms_strict FNE.Family.positive_a
#print axioms FNE.Family.no_wall_inside
#audit_axioms_strict FNE.Family.no_wall_inside
#print axioms FNE.Family.row_carrier_mp
#audit_axioms_strict FNE.Family.row_carrier_mp
#print axioms FNE.Family.row_carrier_mpr
#audit_axioms_strict FNE.Family.row_carrier_mpr
#print axioms FNE.Family.positive_b_row
#audit_axioms_strict FNE.Family.positive_b_row
#print axioms FNE.Family.positive_b_col
#audit_axioms_strict FNE.Family.positive_b_col
#print axioms FNE.Family.next_enc
#audit_axioms_strict FNE.Family.next_enc
#print axioms FNE.Family.caRun_eq
#audit_axioms_strict FNE.Family.caRun_eq
#print axioms FNE.Family.orun_head_le
#audit_axioms_strict FNE.Family.orun_head_le
#print axioms FNE.Family.sim_step
#audit_axioms_strict FNE.Family.sim_step
#print axioms FNE.Family.sim_two
#audit_axioms_strict FNE.Family.sim_two
#print axioms FNE.Family.exists_sim
#audit_axioms_strict FNE.Family.exists_sim
#print axioms FNE.Family.sim_or_back
#audit_axioms_strict FNE.Family.sim_or_back
#print axioms FNE.Family.oHalts_iff
#audit_axioms_strict FNE.Family.oHalts_iff
#print axioms FNE.Family.oRun_oneSided
#audit_axioms_strict FNE.Family.oRun_oneSided
#print axioms FNE.Family.oHalt_init
#audit_axioms_strict FNE.Family.oHalt_init
#print axioms FNE.Family.CA_eq_enc
#audit_axioms_strict FNE.Family.CA_eq_enc
#print axioms FNE.Family.CA_no_halt
#audit_axioms_strict FNE.Family.CA_no_halt
#print axioms FNE.Family.CA_one_one
#audit_axioms_strict FNE.Family.CA_one_one
#print axioms FNE.Family.CA_halt
#audit_axioms_strict FNE.Family.CA_halt
#print axioms FNE.Family.CA_inS
#audit_axioms_strict FNE.Family.CA_inS
#print axioms FNE.Family.tileOf_matchE
#audit_axioms_strict FNE.Family.tileOf_matchE
#print axioms FNE.Family.tileOf_matchN
#audit_axioms_strict FNE.Family.tileOf_matchN
#print axioms FNE.Family.InT.inC
#audit_axioms_strict FNE.Family.InT.inC
#print axioms FNE.Family.leastField_satAt
#audit_axioms_strict FNE.Family.leastField_satAt
#print axioms FNE.Family.seedTile_inT
#audit_axioms_strict FNE.Family.seedTile_inT
#print axioms FNE.Family.horn_b
#audit_axioms_strict FNE.Family.horn_b
#print axioms FNE.Family.LegalFB.inter
#audit_axioms_strict FNE.Family.LegalFB.inter
#print axioms FNE.Family.tileOf_inter
#audit_axioms_strict FNE.Family.tileOf_inter
#print axioms FNE.Family.InT.meet
#audit_axioms_strict FNE.Family.InT.meet
#print axioms FNE.Family.palettes_meet
#audit_axioms_strict FNE.Family.palettes_meet
#print axioms FNE.Family.overlapE
#audit_axioms_strict FNE.Family.overlapE
#print axioms FNE.Family.overlapN
#audit_axioms_strict FNE.Family.overlapN
#print axioms FNE.Family.tileOf_eq_on
#audit_axioms_strict FNE.Family.tileOf_eq_on
#print axioms FNE.Family.horn_c
#audit_axioms_strict FNE.Family.horn_c
#print axioms FNE.Family.isFree_iff_own
#audit_axioms_strict FNE.Family.isFree_iff_own
#print axioms FNE.Family.cen_free
#audit_axioms_strict FNE.Family.cen_free
#print axioms FNE.Family.carrier_iff_nearest
#audit_axioms_strict FNE.Family.carrier_iff_nearest
#print axioms FNE.Family.positive_b_row_all
#audit_axioms_strict FNE.Family.positive_b_row_all
#print axioms FNE.Family.positive_b_col_all
#audit_axioms_strict FNE.Family.positive_b_col_all
#print axioms FNE.Family.positive_c
#audit_axioms_strict FNE.Family.positive_c
#print axioms FNE.Family.seed_at_centres
#audit_axioms_strict FNE.Family.seed_at_centres
#print axioms FNE.Family.fidx_eq
#audit_axioms_strict FNE.Family.fidx_eq
#print axioms FNE.Family.adr_cen
#audit_axioms_strict FNE.Family.adr_cen
#print axioms FNE.Family.adr_succ
#audit_axioms_strict FNE.Family.adr_succ
#print axioms FNE.Family.FTile.toTile_E_W_iff
#audit_axioms_strict FNE.Family.FTile.toTile_E_W_iff
#print axioms FNE.Family.FTile.toTile_N_S_iff
#audit_axioms_strict FNE.Family.FTile.toTile_N_S_iff
#print axioms FNE.Family.toTile_mem_familyR
#audit_axioms_strict FNE.Family.toTile_mem_familyR
#print axioms FNE.Family.payOf_palette
#audit_axioms_strict FNE.Family.payOf_palette
#print axioms FNE.Family.fixE_eq_fixW
#audit_axioms_strict FNE.Family.fixE_eq_fixW
#print axioms FNE.Family.fixN_eq_fixS
#audit_axioms_strict FNE.Family.fixN_eq_fixS
#print axioms FNE.Family.tiles_of_not_halts
#audit_axioms_strict FNE.Family.tiles_of_not_halts
#print axioms FNE.Family.not_ergodic_familyR
#audit_axioms_strict FNE.Family.not_ergodic_familyR
#print axioms FNE.Three.clsN_eq
#audit_axioms_strict FNE.Three.clsN_eq
#print axioms FNE.Three.clsE_eq
#audit_axioms_strict FNE.Three.clsE_eq
#print axioms FNE.Three.clsS_eq
#audit_axioms_strict FNE.Three.clsS_eq
#print axioms FNE.Three.clsW_eq
#audit_axioms_strict FNE.Three.clsW_eq
#print axioms FNE.Three.dMask_eq
#audit_axioms_strict FNE.Three.dMask_eq
#print axioms FNE.Three.letterAt_rootIdx
#audit_axioms_strict FNE.Three.letterAt_rootIdx
#print axioms FNE.Three.ConsistentOn.anti
#audit_axioms_strict FNE.Three.ConsistentOn.anti
#print axioms FNE.Three.testBit_supp_of_fits
#audit_axioms_strict FNE.Three.testBit_supp_of_fits
#print axioms FNE.Three.inv_runCheck
#audit_axioms_strict FNE.Three.inv_runCheck
#print axioms FNE.Three.corner_of_certOK
#audit_axioms_strict FNE.Three.corner_of_certOK
#print axioms FNE.Three.certOK_all
#audit_axioms_strict FNE.Three.certOK_all
#print axioms FNE.Three.corner_lemma
#audit_axioms_strict FNE.Three.corner_lemma
#print axioms FNE.Three.corner_lemma_box
#audit_axioms_strict FNE.Three.corner_lemma_box
#print axioms FNE.Three.corner_lemma_V16
#audit_axioms_strict FNE.Three.corner_lemma_V16
#print axioms FNE.Scaffold.Letter.Fits.thin
#audit_axioms_strict FNE.Scaffold.Letter.Fits.thin
#print axioms FNE.Three.thinRule_add
#audit_axioms_strict FNE.Three.thinRule_add
#print axioms FNE.Three.plane_induction
#audit_axioms_strict FNE.Three.plane_induction
#print axioms FNE.Three.hasThinPhase_of
#audit_axioms_strict FNE.Three.hasThinPhase_of
#print axioms FNE.Three.thr_thin
#audit_axioms_strict FNE.Three.thr_thin
#print axioms FNE.Three.eq_bLetter
#audit_axioms_strict FNE.Three.eq_bLetter
#print axioms FNE.Three.thr_ne_e1
#audit_axioms_strict FNE.Three.thr_ne_e1
#print axioms FNE.Three.thr_ne_e2
#audit_axioms_strict FNE.Three.thr_ne_e2
#print axioms FNE.Three.thr_ne_singleton
#audit_axioms_strict FNE.Three.thr_ne_singleton
#print axioms FNE.Three.thr_zero
#audit_axioms_strict FNE.Three.thr_zero
#print axioms FNE.Three.corner_plane
#audit_axioms_strict FNE.Three.corner_plane
#print axioms FNE.Three.corner_plane_V16
#audit_axioms_strict FNE.Three.corner_plane_V16
#print axioms FNE.Three.CoarseSetup.b_case
#audit_axioms_strict FNE.Three.CoarseSetup.b_case
#print axioms FNE.Three.CoarseSetup.c_case
#audit_axioms_strict FNE.Three.CoarseSetup.c_case
#print axioms FNE.Three.CoarseSetup.d_case
#audit_axioms_strict FNE.Three.CoarseSetup.d_case
#print axioms FNE.Three.CoarseSetup.up_inA
#audit_axioms_strict FNE.Three.CoarseSetup.up_inA
#print axioms FNE.Three.up_inj
#audit_axioms_strict FNE.Three.up_inj
#print axioms FNE.Three.CoarseSetup.coarsen_family
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_family
#print axioms FNE.Three.CoarseSetup.coarsen_thin
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_thin
#print axioms FNE.Three.CoarseSetup.coarsen_ac
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_ac
#print axioms FNE.Three.CoarseSetup.coarsen_phase
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_phase
#print axioms FNE.Three.CoarseSetup.coarsen_singleton
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_singleton
#print axioms FNE.Three.stepL_setup
#audit_axioms_strict FNE.Three.stepL_setup
#print axioms FNE.Three.levels_inv
#audit_axioms_strict FNE.Three.levels_inv
#print axioms FNE.Three.LevelInv.setup
#audit_axioms_strict FNE.Three.LevelInv.setup
#print axioms FNE.Three.levels_top
#audit_axioms_strict FNE.Three.levels_top
#print axioms FNE.Three.levels_family_ac
#audit_axioms_strict FNE.Three.levels_family_ac
#print axioms FNE.Three.levels_letters
#audit_axioms_strict FNE.Three.levels_letters
#print axioms FNE.Three.thin_base
#audit_axioms_strict FNE.Three.thin_base
#print axioms FNE.Three.levels_singleton
#audit_axioms_strict FNE.Three.levels_singleton
#print axioms FNE.Three.promote_lists
#audit_axioms_strict FNE.Three.promote_lists
#print axioms FNE.Three.word_lists
#audit_axioms_strict FNE.Three.word_lists
#print axioms FNE.Three.mem_RM
#audit_axioms_strict FNE.Three.mem_RM
#print axioms FNE.Three.FTile.toTile_injective
#audit_axioms_strict FNE.Three.FTile.toTile_injective
#print axioms FNE.Three.ofTile_spec
#audit_axioms_strict FNE.Three.ofTile_spec
#print axioms FNE.Three.tpar_inA
#audit_axioms_strict FNE.Three.tpar_inA
#print axioms FNE.Three.Q1_E
#audit_axioms_strict FNE.Three.Q1_E
#print axioms FNE.Three.Q1_N
#audit_axioms_strict FNE.Three.Q1_N
#print axioms FNE.Three.Q2_E
#audit_axioms_strict FNE.Three.Q2_E
#print axioms FNE.Three.Q2_N
#audit_axioms_strict FNE.Three.Q2_N
#print axioms FNE.Three.Q2_rulesH
#audit_axioms_strict FNE.Three.Q2_rulesH
#print axioms FNE.Three.Q2_rulesV
#audit_axioms_strict FNE.Three.Q2_rulesV
#print axioms FNE.Three.Q3_E
#audit_axioms_strict FNE.Three.Q3_E
#print axioms FNE.Three.Q3_N
#audit_axioms_strict FNE.Three.Q3_N
#print axioms FNE.Three.Q3_palette
#audit_axioms_strict FNE.Three.Q3_palette
#print axioms FNE.Three.cls_E
#audit_axioms_strict FNE.Three.cls_E
#print axioms FNE.Three.cls_N
#audit_axioms_strict FNE.Three.cls_N
#print axioms FNE.Three.quad_of_cls
#audit_axioms_strict FNE.Three.quad_of_cls
#print axioms FNE.Three.ctr_of_compatible
#audit_axioms_strict FNE.Three.ctr_of_compatible
#print axioms FNE.Three.ctr_match_e1
#audit_axioms_strict FNE.Three.ctr_match_e1
#print axioms FNE.Three.ctr_match_e1'
#audit_axioms_strict FNE.Three.ctr_match_e1'
#print axioms FNE.Three.ctr_match_e2
#audit_axioms_strict FNE.Three.ctr_match_e2
#print axioms FNE.Three.ctr_match_e2'
#audit_axioms_strict FNE.Three.ctr_match_e2'
#print axioms FNE.Three.cls_block
#audit_axioms_strict FNE.Three.cls_block
#print axioms FNE.Three.thr_move
#audit_axioms_strict FNE.Three.thr_move
#print axioms FNE.Three.walk_token
#audit_axioms_strict FNE.Three.walk_token
#print axioms FNE.Three.thr_phase
#audit_axioms_strict FNE.Three.thr_phase
#print axioms FNE.Three.classPart_safe
#audit_axioms_strict FNE.Three.classPart_safe
#print axioms FNE.Three.exists_classPart
#audit_axioms_strict FNE.Three.exists_classPart
#print axioms FNE.Three.walker_move
#audit_axioms_strict FNE.Three.walker_move
#print axioms FNE.Three.walker_total
#audit_axioms_strict FNE.Three.walker_total
#print axioms FNE.Three.walker_pin1
#audit_axioms_strict FNE.Three.walker_pin1
#print axioms FNE.Three.walker_pin2
#audit_axioms_strict FNE.Three.walker_pin2
#print axioms FNE.Three.pin_clone_two
#audit_axioms_strict FNE.Three.pin_clone_two
#print axioms FNE.Three.pin_clone_one
#audit_axioms_strict FNE.Three.pin_clone_one
#print axioms FNE.Three.pin_clone_both
#audit_axioms_strict FNE.Three.pin_clone_both
#print axioms FNE.Three.quad_iota
#audit_axioms_strict FNE.Three.quad_iota
#print axioms FNE.Three.lists_family
#audit_axioms_strict FNE.Three.lists_family
#print axioms FNE.Three.lists_ac
#audit_axioms_strict FNE.Three.lists_ac
#print axioms FNE.Three.lists_pin1
#audit_axioms_strict FNE.Three.lists_pin1
#print axioms FNE.Three.lists_pin2
#audit_axioms_strict FNE.Three.lists_pin2
#print axioms FNE.Three.dyadicSetup_of
#audit_axioms_strict FNE.Three.dyadicSetup_of
#print axioms FNE.Three.thr_start
#audit_axioms_strict FNE.Three.thr_start
#print axioms FNE.Three.thr_promote
#audit_axioms_strict FNE.Three.thr_promote
#print axioms FNE.Three.thr_word
#audit_axioms_strict FNE.Three.thr_word
#print axioms FNE.Three.exists_cornerPair
#audit_axioms_strict FNE.Three.exists_cornerPair
#print axioms FNE.Three.quad_cell
#audit_axioms_strict FNE.Three.quad_cell
#print axioms FNE.Three.cell_par
#audit_axioms_strict FNE.Three.cell_par
#print axioms FNE.Three.WordSetup.quarters
#audit_axioms_strict FNE.Three.WordSetup.quarters
#print axioms FNE.Three.WordSetup.walk_right
#audit_axioms_strict FNE.Three.WordSetup.walk_right
#print axioms FNE.Three.WordSetup.walk_left
#audit_axioms_strict FNE.Three.WordSetup.walk_left
#print axioms FNE.Three.WordSetup.walk_up
#audit_axioms_strict FNE.Three.WordSetup.walk_up
#print axioms FNE.Three.WordSetup.walk_down
#audit_axioms_strict FNE.Three.WordSetup.walk_down
#print axioms FNE.Three.corridor
#audit_axioms_strict FNE.Three.corridor
#print axioms FNE.Three.WordSetup.roles_h
#audit_axioms_strict FNE.Three.WordSetup.roles_h
#print axioms FNE.Three.WordSetup.roles_v
#audit_axioms_strict FNE.Three.WordSetup.roles_v
#print axioms FNE.Three.payInf_mem
#audit_axioms_strict FNE.Three.payInf_mem
#print axioms FNE.Three.payInf_EW
#audit_axioms_strict FNE.Three.payInf_EW
#print axioms FNE.Three.payInf_NS
#audit_axioms_strict FNE.Three.payInf_NS
#print axioms FNE.Three.meet_E
#audit_axioms_strict FNE.Three.meet_E
#print axioms FNE.Three.meet_N
#audit_axioms_strict FNE.Three.meet_N
#print axioms FNE.Three.exists_enum
#audit_axioms_strict FNE.Three.exists_enum
#print axioms FNE.Three.Pal_meet
#audit_axioms_strict FNE.Three.Pal_meet
#print axioms FNE.Three.WordSetup.pal_of_walker
#audit_axioms_strict FNE.Three.WordSetup.pal_of_walker
#print axioms FNE.Three.WordSetup.pal_mv
#audit_axioms_strict FNE.Three.WordSetup.pal_mv
#print axioms FNE.Three.WordSetup.row_chain
#audit_axioms_strict FNE.Three.WordSetup.row_chain
#print axioms FNE.Three.WordSetup.col_chain
#audit_axioms_strict FNE.Three.WordSetup.col_chain
#print axioms FNE.Three.three_of_board
#audit_axioms_strict FNE.Three.three_of_board
#print axioms FNE.Three.leftEnd_in_J
#audit_axioms_strict FNE.Three.leftEnd_in_J
#print axioms FNE.Three.rightEnd_in_J
#audit_axioms_strict FNE.Three.rightEnd_in_J
#print axioms FNE.Three.exists_rank_zero
#audit_axioms_strict FNE.Three.exists_rank_zero
#print axioms FNE.Three.wordTower_rel
#audit_axioms_strict FNE.Three.wordTower_rel
#print axioms FNE.Three.sigmaPow_inA
#audit_axioms_strict FNE.Three.sigmaPow_inA
#print axioms FNE.Three.word_vwall
#audit_axioms_strict FNE.Three.word_vwall
#print axioms FNE.Three.word_hwall
#audit_axioms_strict FNE.Three.word_hwall
#print axioms FNE.Three.line_nowall
#audit_axioms_strict FNE.Three.line_nowall
#print axioms FNE.Three.line_corridor
#audit_axioms_strict FNE.Three.line_corridor
#print axioms FNE.Three.resSet_spec
#audit_axioms_strict FNE.Three.resSet_spec
#print axioms FNE.Three.card_resSet
#audit_axioms_strict FNE.Three.card_resSet
#print axioms FNE.Three.bFree_two_bD_add
#audit_axioms_strict FNE.Three.bFree_two_bD_add
#print axioms FNE.Three.many_free
#audit_axioms_strict FNE.Three.many_free
#print axioms FNE.Three.word_seed
#audit_axioms_strict FNE.Three.word_seed
#print axioms FNE.Three.board
#audit_axioms_strict FNE.Three.board
#print axioms FNE.Three.three_tokens
#audit_axioms_strict FNE.Three.three_tokens
#print axioms FNE.Three.theoremC_familyR
#audit_axioms_strict FNE.Three.theoremC_familyR
#print axioms FNE.Three.eight_familyR
#audit_axioms_strict FNE.Three.eight_familyR
#print axioms FNE.Three.cor_eight_of_computable
#audit_axioms_strict FNE.Three.cor_eight_of_computable
#print axioms FNE.Family.colCode_injective
#audit_axioms_strict FNE.Family.colCode_injective
#print axioms FNE.Family.colCodeL_eq
#audit_axioms_strict FNE.Family.colCodeL_eq
#print axioms FNE.Family.payList_eq
#audit_axioms_strict FNE.Family.payList_eq
#print axioms FNE.Family.seedTile_indep
#audit_axioms_strict FNE.Family.seedTile_indep
#print axioms FNE.Family.tileOf_congr
#audit_axioms_strict FNE.Family.tileOf_congr
#print axioms FNE.Family.SatAt.congr_box
#audit_axioms_strict FNE.Family.SatAt.congr_box
#print axioms FNE.Family.satAt_iff
#audit_axioms_strict FNE.Family.satAt_iff
#print axioms FNE.Family.sat_iff
#audit_axioms_strict FNE.Family.sat_iff
#print axioms FNE.Family.tileOf_lists
#audit_axioms_strict FNE.Family.tileOf_lists
#print axioms FNE.Family.inT_iff
#audit_axioms_strict FNE.Family.inT_iff
#print axioms FNE.Family.palette_iff
#audit_axioms_strict FNE.Family.palette_iff
#print axioms FNE.Family.familyR_eq
#audit_axioms_strict FNE.Family.familyR_eq
#print axioms FNE.Family.primrec_sublists
#audit_axioms_strict FNE.Family.primrec_sublists
#print axioms FNE.Family.primrec_oTr
#audit_axioms_strict FNE.Family.primrec_oTr
#print axioms FNE.Family.primrec_next
#audit_axioms_strict FNE.Family.primrec_next
#print axioms FNE.Family.primrec_quads
#audit_axioms_strict FNE.Family.primrec_quads
#print axioms FNE.Family.primrecPred_actChk
#audit_axioms_strict FNE.Family.primrecPred_actChk
#print axioms FNE.Family.primrec_familyR
#audit_axioms_strict FNE.Family.primrec_familyR
#print axioms FNE.Family.computable_familyR
#audit_axioms_strict FNE.Family.computable_familyR
#print axioms FNE.not_computable_ergodic_of
#audit_axioms_strict FNE.not_computable_ergodic_of
#print axioms FNE.not_computable_ergodic
#audit_axioms_strict FNE.not_computable_ergodic
#print axioms FNE.not_computable_halts_of_compiler
#audit_axioms_strict FNE.not_computable_halts_of_compiler
#print axioms FNE.cor_eight_undecidable_of_compiler
#audit_axioms_strict FNE.cor_eight_undecidable_of_compiler
#print axioms FNE.Compiler.lookup_eq_some
#audit_axioms_strict FNE.Compiler.lookup_eq_some
#print axioms FNE.Compiler.symNum_default
#audit_axioms_strict FNE.Compiler.symNum_default
#print axioms FNE.Compiler.symNum_injective
#audit_axioms_strict FNE.Compiler.symNum_injective
#print axioms FNE.Compiler.stIdx_inj
#audit_axioms_strict FNE.Compiler.stIdx_inj
#print axioms FNE.Compiler.lookup_state
#audit_axioms_strict FNE.Compiler.lookup_state
#print axioms FNE.Compiler.lookup_pre
#audit_axioms_strict FNE.Compiler.lookup_pre
#print axioms FNE.Compiler.step_rel
#audit_axioms_strict FNE.Compiler.step_rel
#print axioms FNE.Compiler.step_halt
#audit_axioms_strict FNE.Compiler.step_halt
#print axioms FNE.Compiler.reaches_rel
#audit_axioms_strict FNE.Compiler.reaches_rel
#print axioms FNE.Compiler.prefix_run
#audit_axioms_strict FNE.Compiler.prefix_run
#print axioms FNE.Compiler.prefix_done
#audit_axioms_strict FNE.Compiler.prefix_done
#print axioms FNE.Compiler.mk₁_nth
#audit_axioms_strict FNE.Compiler.mk₁_nth
#print axioms FNE.Compiler.rel_init
#audit_axioms_strict FNE.Compiler.rel_init
#print axioms FNE.Compiler.compile_halts
#audit_axioms_strict FNE.Compiler.compile_halts
#print axioms FNE.Compiler.primrec_pre
#audit_axioms_strict FNE.Compiler.primrec_pre
#print axioms FNE.Compiler.primrec_mkMachine
#audit_axioms_strict FNE.Compiler.primrec_mkMachine
#print axioms FNE.Compiler.bin_eq
#audit_axioms_strict FNE.Compiler.bin_eq
#print axioms FNE.Compiler.trNat_eq
#audit_axioms_strict FNE.Compiler.trNat_eq
#print axioms FNE.Compiler.primrec_bin
#audit_axioms_strict FNE.Compiler.primrec_bin
#print axioms FNE.Compiler.univFun_partrec
#audit_axioms_strict FNE.Compiler.univFun_partrec
#print axioms FNE.Compiler.univCode_eval
#audit_axioms_strict FNE.Compiler.univCode_eval
#print axioms FNE.Compiler.supports₀
#audit_axioms_strict FNE.Compiler.supports₀
#print axioms FNE.Compiler.init_eq
#audit_axioms_strict FNE.Compiler.init_eq
#print axioms FNE.Compiler.eval_dom
#audit_axioms_strict FNE.Compiler.eval_dom
#print axioms FNE.Compiler.compiler_halts
#audit_axioms_strict FNE.Compiler.compiler_halts
#print axioms FNE.Compiler.input_map
#audit_axioms_strict FNE.Compiler.input_map
#print axioms FNE.Compiler.primrec_compiler
#audit_axioms_strict FNE.Compiler.primrec_compiler
#print axioms FNE.Compiler.computable_compiler
#audit_axioms_strict FNE.Compiler.computable_compiler

/-! Complete imported-project audit, including generated and private declarations. -/
set_option maxHeartbeats 20000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx]!
      if mod.toString.startsWith "FixedNoiseErgodicity" then
        if ci matches .axiomInfo _ then throwError "Project axiom declaration {n}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        logInfo m!"FNE_DECL:{toJson (n.toString, mod.toString, ax.map Name.toString) |>.compress}"
        count := count + 1
  let some main := env.find? ``FNE.cor_eight | throwError "Missing cor_eight"
  unless main.type == mkConst ``FNE.CorEight do throwError "cor_eight statement changed"
  logInfo m!"FNE_DECL_COUNT:{count}"
