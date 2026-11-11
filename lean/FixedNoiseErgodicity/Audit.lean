/-
# Axiom audit

Allowed: `propext`, `Classical.choice`, `Quot.sound`; any other axiom, and `sorryAx`, is a
compile error (`#audit_axioms_strict`). Since session 9 the core theorem `cor_eight` is
sorry-free and audited strictly.
Also run `scripts/lint.sh`, which rejects `native_decide`, `implemented_by`, `extern`, `axiom`
declarations and `autoImplicit true` anywhere in the sources.
-/
import FixedNoiseErgodicity.AuditCommand
import FixedNoiseErgodicity.Statements
import FixedNoiseErgodicity.Basic
import FixedNoiseErgodicity.Section2.TokenGame
import FixedNoiseErgodicity.Section4.Deterministic
import FixedNoiseErgodicity.Combinatorics.EdgeCount
import FixedNoiseErgodicity.Section3.Transport
import FixedNoiseErgodicity.Section3.Graph
import FixedNoiseErgodicity.Combinatorics.Contour
import FixedNoiseErgodicity.Section3.Contour
import FixedNoiseErgodicity.Section2.Process
import FixedNoiseErgodicity.Section2.Markov
import FixedNoiseErgodicity.Section2.Ergodic
import FixedNoiseErgodicity.Section3.Constants
import FixedNoiseErgodicity.Section3.Peierls
import FixedNoiseErgodicity.Section4.Memory
import FixedNoiseErgodicity.Section3.Forgetting
import FixedNoiseErgodicity.Section2.Feller
import FixedNoiseErgodicity.Section2.ForgetErgodic
import FixedNoiseErgodicity.Section2.PCA
import FixedNoiseErgodicity.TheoremB
import FixedNoiseErgodicity.Section2.Compact
import FixedNoiseErgodicity.Scaffold.WangSet
import FixedNoiseErgodicity.Scaffold.Facts
import FixedNoiseErgodicity.Scaffold.Format
import FixedNoiseErgodicity.Family.Positive
import FixedNoiseErgodicity.Family.Machine
import FixedNoiseErgodicity.Family.Horn
import FixedNoiseErgodicity.Family.HornHalt
import FixedNoiseErgodicity.Family.Free
import FixedNoiseErgodicity.Family.FamilyR
import FixedNoiseErgodicity.Family.NonHalting
import FixedNoiseErgodicity.Three.Corner
import FixedNoiseErgodicity.Three.Lists
import FixedNoiseErgodicity.Three.Coarse
import FixedNoiseErgodicity.Three.Dyadic
import FixedNoiseErgodicity.Three.Pairs
import FixedNoiseErgodicity.Three.Interface
import FixedNoiseErgodicity.Three.Walker
import FixedNoiseErgodicity.Three.Promote
import FixedNoiseErgodicity.Three.Final
import FixedNoiseErgodicity.Three.Board
import FixedNoiseErgodicity.Three.Assembly
import FixedNoiseErgodicity.Family.Codes
import FixedNoiseErgodicity.Family.Decide
import FixedNoiseErgodicity.Family.Computable
import FixedNoiseErgodicity.Main
import FixedNoiseErgodicity.Bridge
import FixedNoiseErgodicity.Undecidable

set_option autoImplicit false

/-! ## The core statement -/

#print axioms FNE.cor_eight
#audit_axioms_strict FNE.cor_eight

/-! ## "Undecidable" as a theorem (D1, session 10; `Undecidable.lean`) -/

#print axioms FNE.cor_eight_undecidable_statement
#audit_axioms_strict FNE.cor_eight_undecidable_statement
#print axioms FNE.cor_eight_undecidable
#audit_axioms_strict FNE.cor_eight_undecidable
#print axioms FNE.nonergodic_not_re
#audit_axioms_strict FNE.nonergodic_not_re
#print axioms FNE.halts_not_computable
#audit_axioms_strict FNE.halts_not_computable
#audit_axioms_strict FNE.not_halts_not_re

/-! ## Proved leaves (must stay free of `sorryAx`) -/

#audit_axioms_strict FNE.eps0_eq
#audit_axioms_strict FNE.quorum_unique
#audit_axioms_strict FNE.quorumRule_eq_live_iff
#audit_axioms_strict FNE.quorumRule_eq_bot_iff

-- Section 2 (token game)
#audit_axioms_strict FNE.TokenGame.refutable_iff_not_exists_planeSafe
#audit_axioms_strict FNE.TokenGame.not_refutable_of_tiles
#audit_axioms_strict FNE.TokenGame.walk
#audit_axioms_strict FNE.TokenGame.safe_subset_tables
#audit_axioms_strict FNE.TokenGame.limitTable_safe

-- Section 4 (memory), deterministic part
#audit_axioms_strict FNE.checkAll_eq_cloned
#audit_axioms_strict FNE.quorumRule_cloned
#audit_axioms_strict FNE.providers_of_live
#audit_axioms_strict FNE.two_bad_parents_cloned
#audit_axioms_strict FNE.two_bad_parents_bot
#audit_axioms_strict FNE.dominate_cloned
#audit_axioms_strict FNE.dominate_bot

-- mem:count = fgt:count
#audit_axioms_strict FNE.EdgeCount.exists_covering_walk
#audit_axioms_strict FNE.EdgeCount.card_le_pow

-- Section 3 (forgetting), deterministic chain
#audit_axioms_strict FNE.mem_inst_of_family
#audit_axioms_strict FNE.presentFamily_closed
#audit_axioms_strict FNE.transport
#audit_axioms_strict FNE.cover
#audit_axioms_strict FNE.live_marked

-- fgt:count instantiated for the graph 𝒢
#audit_axioms_strict FNE.gCount
#audit_axioms_strict FNE.gCount_D0
#audit_axioms_strict FNE.finite_connected

-- lem:contour (abstract core and the instance on 𝒢)
#audit_axioms_strict FNE.Contour.SupportSystem.exists_bij
#audit_axioms_strict FNE.Contour.SupportSystem.contour
#audit_axioms_strict FNE.psiG_sum
#audit_axioms_strict FNE.psiG_step
#audit_axioms_strict FNE.contourG
#audit_axioms_strict FNE.contour_marked

-- Section 2.2: the process (measure plumbing)
#audit_axioms_strict FNE.isProbabilityMeasure_noiseLaw
#audit_axioms_strict FNE.quorumRule_local
#audit_axioms_strict FNE.measurable_run
#audit_axioms_strict FNE.isProbabilityMeasure_law
#audit_axioms_strict FNE.law_zero
#audit_axioms_strict FNE.law_apply_eq_lintegral
#audit_axioms_strict FNE.noiseLaw_flags_eq
#audit_axioms_strict FNE.noiseLaw_map_splitN
#audit_axioms_strict FNE.law_dirac_one
#audit_axioms_strict FNE.law_succ'
#audit_axioms_strict FNE.law_succ
#audit_axioms_strict FNE.siteLaw_pos

-- Section 2.3: memory excludes ergodicity (D8, direct)
#audit_axioms_strict FNE.not_ergodic_of_memory

-- vertices of a connected edge set (for the Peierls sums)
#audit_axioms_strict FNE.EdgeCount.exists_vertices

-- Constants (fgt:rem-constants, thm:memory)
#audit_axioms_strict FNE.eps0_eq_epsK
#audit_axioms_strict FNE.beta_le_half
#audit_axioms_strict FNE.lam_le
#audit_axioms_strict FNE.memoryBound_lt

-- The Peierls sum (Sections 3.6, 4.4)
#audit_axioms_strict FNE.noiseLaw_allEvents_le
#audit_axioms_strict FNE.peierls

-- Section 4 (memory)
#audit_axioms_strict FNE.field_bound
#audit_axioms_strict FNE.memory
#audit_axioms_strict FNE.hasMemory_of_tiling
#audit_axioms_strict FNE.not_ergodic_of_tiles

-- Section 3 (forgetting)
#audit_axioms_strict FNE.discrepancy_path
#audit_axioms_strict FNE.slabs
#audit_axioms_strict FNE.packing
#audit_axioms_strict FNE.forgetting
#audit_axioms_strict FNE.forgetting_tv
#audit_axioms_strict FNE.forgets_of_refutable

-- Section 2.3: Feller, invariant measures, weak convergence on cylinders
#audit_axioms_strict FNE.continuous_run
#audit_axioms_strict FNE.integral_law
#audit_axioms_strict FNE.continuous_Phi
#audit_axioms_strict FNE.isInvariant_of_cesaro_limit
#audit_axioms_strict FNE.exists_cesaro_limit
#audit_axioms_strict FNE.exists_invariant
#audit_axioms_strict FNE.exists_window_approx
#audit_axioms_strict FNE.weakTendsto_of_cyl
#audit_axioms_strict FNE.weakTendsto_iff_cyl
#audit_axioms_strict FNE.weakTendsto_iff_dtv

-- Section 2.3: forgetting implies ergodicity; memory gives two invariant measures
#audit_axioms_strict FNE.law_toReal_eq_integral
#audit_axioms_strict FNE.dtv_law_le
#audit_axioms_strict FNE.ergodic_of_forgets
#audit_axioms_strict FNE.two_invariant_of_memory

-- Section 2.2: positive-rate PCA (all four clauses)
#audit_axioms_strict FNE.quorumRule_translate
#audit_axioms_strict FNE.isPositiveRatePCA

-- Theorem B, the halves of Theorem A, and the interface to Theorem C
#audit_axioms_strict FNE.ergodic_of_refutable
#audit_axioms_strict FNE.theoremB
#audit_axioms_strict FNE.eight_of_dichotomy
#audit_axioms_strict FNE.cor_eight_of_theoremC

-- Section 2.1: legal patterns, set:compact (session 4)
#audit_axioms_strict FNE.isTiling_iff_isLegalPattern
#audit_axioms_strict FNE.tiles_of_forall_box
#audit_axioms_strict FNE.tiles_of_forall_square
#audit_axioms_strict FNE.compact

-- Section 5 and Appendix A: tables (session 4)
#audit_axioms_strict FNE.Scaffold.F_epN
#audit_axioms_strict FNE.Scaffold.F_epS
#audit_axioms_strict FNE.Scaffold.F_epE
#audit_axioms_strict FNE.Scaffold.F_epW
#audit_axioms_strict FNE.Scaffold.F_injective
#audit_axioms_strict FNE.Scaffold.thin_matchE_iff
#audit_axioms_strict FNE.Scaffold.thin_matchN_iff
#audit_axioms_strict FNE.Scaffold.se_spec
#audit_axioms_strict FNE.Scaffold.se_unique
#audit_axioms_strict FNE.Scaffold.nw_spec
#audit_axioms_strict FNE.Scaffold.nw_unique
#audit_axioms_strict FNE.Scaffold.Formal.baseList_length
#audit_axioms_strict FNE.Scaffold.Formal.tab_alphabet_rows
#audit_axioms_strict FNE.Scaffold.Formal.InO.corner
#audit_axioms_strict FNE.Scaffold.Formal.col_injective
#audit_axioms_strict FNE.Scaffold.Letter.letters_length
#audit_axioms_strict FNE.Scaffold.Letter.letters_nodup
#audit_axioms_strict FNE.Scaffold.Letter.tab_letters_rows
#audit_axioms_strict FNE.Scaffold.Letter.col_injective
#audit_axioms_strict FNE.Scaffold.Letter.MatchN.b1_eq
#audit_axioms_strict FNE.Scaffold.Letter.MatchE.b2_eq

-- Section 5: substitutions (session 4)
#audit_axioms_strict FNE.Scaffold.legalOn_subst2_iff
#audit_axioms_strict FNE.Scaffold.Formal.InO.child
#audit_axioms_strict FNE.Scaffold.Formal.phi_legal
#audit_axioms_strict FNE.Scaffold.Formal.legalOn_phi_iff
#audit_axioms_strict FNE.Scaffold.Formal.child_injective
#audit_axioms_strict FNE.Scaffold.Letter.InA.child
#audit_axioms_strict FNE.Scaffold.Letter.phi'_legal
#audit_axioms_strict FNE.Scaffold.Letter.legalOn_phi'_iff
#audit_axioms_strict FNE.Scaffold.Letter.child_injective
#audit_axioms_strict FNE.Scaffold.phi'_iterate_two_mul
#audit_axioms_strict FNE.Scaffold.legalOn_sigma_iff
#audit_axioms_strict FNE.Scaffold.sigmaPow_legal
#audit_axioms_strict FNE.Scaffold.sigma_injective
#audit_axioms_strict FNE.Scaffold.sigma_bits
#audit_axioms_strict FNE.Scaffold.iterate_sigmaPat_block
#audit_axioms_strict FNE.Scaffold.sigmaPow_succ_apply

-- Section 5: the scaffold as a Wang set (session 4)
#audit_axioms_strict FNE.Scaffold.Letter.toTile_injective
#audit_axioms_strict FNE.Scaffold.card_scaffoldSet
#audit_axioms_strict FNE.Scaffold.scaffold_tiles
#audit_axioms_strict FNE.Scaffold.exists_letter_tiling
#audit_axioms_strict FNE.Scaffold.fit_pairs_count

-- Facts read off the tables, used in Sections 6 and 9 (session 4)
#audit_axioms_strict FNE.Scaffold.Thin.epE_eq_epW_iff
#audit_axioms_strict FNE.Scaffold.Thin.epN_eq_epS_iff
#audit_axioms_strict FNE.Scaffold.Thin.F_epE_eq_F_epW_iff
#audit_axioms_strict FNE.Scaffold.Thin.F_epN_eq_F_epS_iff
#audit_axioms_strict FNE.Scaffold.Thin.four_distinct
#audit_axioms_strict FNE.Scaffold.Letter.InA.cornerLetter
#audit_axioms_strict FNE.Scaffold.Letter.InA.thin_b
#audit_axioms_strict FNE.Scaffold.T1
#audit_axioms_strict FNE.Scaffold.T2
#audit_axioms_strict FNE.Scaffold.T3_c
#audit_axioms_strict FNE.Scaffold.T3_d
#audit_axioms_strict FNE.Scaffold.T3_bits
#audit_axioms_strict FNE.Scaffold.T4
#audit_axioms_strict FNE.Scaffold.T5_black
#audit_axioms_strict FNE.Scaffold.T5_letter
#audit_axioms_strict FNE.Scaffold.corner_red_endpoints

-- Data format of the corner-lemma certificate (design; session 4)
#audit_axioms_strict FNE.Scaffold.letterAt_inA
#audit_axioms_strict FNE.Scaffold.exists_letterAt
#audit_axioms_strict FNE.Scaffold.letterAt_injective
#audit_axioms_strict FNE.Scaffold.Letter.fits_iff
#audit_axioms_strict FNE.Scaffold.fitCode_iff
#audit_axioms_strict FNE.Scaffold.testBit_listMask
#audit_axioms_strict FNE.Scaffold.testBit_letterMask
#audit_axioms_strict FNE.Scaffold.letterMask_eq_zero_iff
#audit_axioms_strict FNE.Scaffold.testBit_fitMask

-- Section 6.1: towers, digits, ranks, red paths (session 5)
#audit_axioms_strict FNE.Family.eq_digits
#audit_axioms_strict FNE.Family.emod_eq_wsum_dig
#audit_axioms_strict FNE.Family.IsRank.emod
#audit_axioms_strict FNE.Family.isRank_of_emod
#audit_axioms_strict FNE.Family.IsLetterTiling.sub
#audit_axioms_strict FNE.Family.exists_tower
#audit_axioms_strict FNE.Family.TowerRel.chain
#audit_axioms_strict FNE.Family.rank_bits_col
#audit_axioms_strict FNE.Family.rank_bits_row
#audit_axioms_strict FNE.Family.red_chain_col
#audit_axioms_strict FNE.Family.red_chain_row
#audit_axioms_strict FNE.Family.red_col
#audit_axioms_strict FNE.Family.red_row

-- Section 6.2: quarters, walls, frames (session 5)
#audit_axioms_strict FNE.Family.SPair.matchE_iff
#audit_axioms_strict FNE.Family.SPair.matchN_iff
#audit_axioms_strict FNE.Family.legalOn_quarter_iff
#audit_axioms_strict FNE.Family.IsLetterTiling.quarter
#audit_axioms_strict FNE.Family.inFrame_iff
#audit_axioms_strict FNE.Family.isLeftEnd_iff
#audit_axioms_strict FNE.Family.isRightEnd_iff
#audit_axioms_strict FNE.Family.rank_of_endpoint
#audit_axioms_strict FNE.Family.walls_col
#audit_axioms_strict FNE.Family.walls_row

-- Section 6.3: frames, laminar families, the phase 1/3 (session 5)
#audit_axioms_strict FNE.Family.FrameOffsets.emod
#audit_axioms_strict FNE.Family.frameOffsets_tower
#audit_axioms_strict FNE.Family.frame_window_unique
#audit_axioms_strict FNE.Family.endpoint_not_inFrame
#audit_axioms_strict FNE.Family.frames_nested
#audit_axioms_strict FNE.Family.frames_contain
#audit_axioms_strict FNE.Family.Laminar.endpoint_unique
#audit_axioms_strict FNE.Family.Laminar.mem_of_consecutive
#audit_axioms_strict FNE.Family.Laminar.consecutive_of_minimal
#audit_axioms_strict FNE.Family.three_wsum_third
#audit_axioms_strict FNE.Family.three_wsum_third_emod
#audit_axioms_strict FNE.Family.three_towerOffsets_third
#audit_axioms_strict FNE.Family.exists_interior_third
#audit_axioms_strict FNE.Family.exists_rank_third
#audit_axioms_strict FNE.Family.own_spec

-- Sections 6.2 and 6.4: routed scaffold, prop:routing, fam:positive (a) (session 5)
#audit_axioms_strict FNE.Family.not_carrier_of_wall
#audit_axioms_strict FNE.Family.routing
#audit_axioms_strict FNE.Family.lineFlow_rules
#audit_axioms_strict FNE.Family.rowWall_iff
#audit_axioms_strict FNE.Family.colWall_iff
#audit_axioms_strict FNE.Family.positive_a
#audit_axioms_strict FNE.Family.no_wall_inside
#audit_axioms_strict FNE.Family.row_carrier_mp
#audit_axioms_strict FNE.Family.row_carrier_mpr
#audit_axioms_strict FNE.Family.positive_b_row
#audit_axioms_strict FNE.Family.positive_b_col

-- Section 6.6: the one-sided machine M° ([gap] 06:281 resolved, D10), the CA (session 6)
#audit_axioms_strict FNE.Family.next_enc
#audit_axioms_strict FNE.Family.caRun_eq
#audit_axioms_strict FNE.Family.orun_head_le
#audit_axioms_strict FNE.Family.sim_step
#audit_axioms_strict FNE.Family.sim_two
#audit_axioms_strict FNE.Family.exists_sim
#audit_axioms_strict FNE.Family.sim_or_back
#audit_axioms_strict FNE.Family.oHalts_iff
#audit_axioms_strict FNE.Family.oRun_oneSided
#audit_axioms_strict FNE.Family.oHalt_init
#audit_axioms_strict FNE.Family.CA_eq_enc
#audit_axioms_strict FNE.Family.CA_no_halt
#audit_axioms_strict FNE.Family.CA_one_one
#audit_axioms_strict FNE.Family.CA_halt
#audit_axioms_strict FNE.Family.CA_inS

-- Section 6.6: the pointed Horn layer (session 6)
#audit_axioms_strict FNE.Family.tileOf_matchE
#audit_axioms_strict FNE.Family.tileOf_matchN
#audit_axioms_strict FNE.Family.InT.inC
#audit_axioms_strict FNE.Family.leastField_satAt
#audit_axioms_strict FNE.Family.seedTile_inT
#audit_axioms_strict FNE.Family.horn_b
#audit_axioms_strict FNE.Family.LegalFB.inter
#audit_axioms_strict FNE.Family.tileOf_inter
#audit_axioms_strict FNE.Family.InT.meet
#audit_axioms_strict FNE.Family.palettes_meet
#audit_axioms_strict FNE.Family.overlapE
#audit_axioms_strict FNE.Family.overlapN
#audit_axioms_strict FNE.Family.tileOf_eq_on
#audit_axioms_strict FNE.Family.horn_c

-- Sections 6.3-6.4: free coordinates, fam:positive (b), (c) for every tiling, addresses (session 6)
#audit_axioms_strict FNE.Family.isFree_iff_own
#audit_axioms_strict FNE.Family.cen_free
#audit_axioms_strict FNE.Family.carrier_iff_nearest
#audit_axioms_strict FNE.Family.positive_b_row_all
#audit_axioms_strict FNE.Family.positive_b_col_all
#audit_axioms_strict FNE.Family.positive_c
#audit_axioms_strict FNE.Family.seed_at_centres
#audit_axioms_strict FNE.Family.fidx_eq
#audit_axioms_strict FNE.Family.adr_cen
#audit_axioms_strict FNE.Family.adr_succ

-- Section 6.7: def:family and prop:tiles (session 6)
#audit_axioms_strict FNE.Family.FTile.toTile_E_W_iff
#audit_axioms_strict FNE.Family.FTile.toTile_N_S_iff
#audit_axioms_strict FNE.Family.toTile_mem_familyR
#audit_axioms_strict FNE.Family.payOf_palette
#audit_axioms_strict FNE.Family.fixE_eq_fixW
#audit_axioms_strict FNE.Family.fixN_eq_fixS
#audit_axioms_strict FNE.Family.tiles_of_not_halts
#audit_axioms_strict FNE.Family.not_ergodic_familyR

-- Section 9.3: the corner lemma, kernel-checked certificate on V_6 (session 7)
#audit_axioms_strict FNE.Three.clsN_eq
#audit_axioms_strict FNE.Three.clsE_eq
#audit_axioms_strict FNE.Three.clsS_eq
#audit_axioms_strict FNE.Three.clsW_eq
#audit_axioms_strict FNE.Three.dMask_eq
#audit_axioms_strict FNE.Three.letterAt_rootIdx
#audit_axioms_strict FNE.Three.ConsistentOn.anti
#audit_axioms_strict FNE.Three.testBit_supp_of_fits
#audit_axioms_strict FNE.Three.inv_runCheck
#audit_axioms_strict FNE.Three.corner_of_certOK
#audit_axioms_strict FNE.Three.certOK_all
#audit_axioms_strict FNE.Three.corner_lemma
#audit_axioms_strict FNE.Three.corner_lemma_box
#audit_axioms_strict FNE.Three.corner_lemma_V16

-- Section 9.2-9.3: list families, thr:thin, thr:ne, thr:zero, thr:corner-plane (session 7)
#audit_axioms_strict FNE.Scaffold.Letter.Fits.thin
#audit_axioms_strict FNE.Three.thinRule_add
#audit_axioms_strict FNE.Three.plane_induction
#audit_axioms_strict FNE.Three.hasThinPhase_of
#audit_axioms_strict FNE.Three.thr_thin
#audit_axioms_strict FNE.Three.eq_bLetter
#audit_axioms_strict FNE.Three.thr_ne_e1
#audit_axioms_strict FNE.Three.thr_ne_e2
#audit_axioms_strict FNE.Three.thr_ne_singleton
#audit_axioms_strict FNE.Three.thr_zero
#audit_axioms_strict FNE.Three.corner_plane
#audit_axioms_strict FNE.Three.corner_plane_V16

-- Section 9.2: thr:coarse (session 7)
#audit_axioms_strict FNE.Three.CoarseSetup.b_case
#audit_axioms_strict FNE.Three.CoarseSetup.c_case
#audit_axioms_strict FNE.Three.CoarseSetup.d_case
#audit_axioms_strict FNE.Three.CoarseSetup.up_inA
#audit_axioms_strict FNE.Three.up_inj
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_family
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_thin
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_ac
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_phase
#audit_axioms_strict FNE.Three.CoarseSetup.coarsen_singleton

-- Section 9.2: thr:dyadic (session 7)
#audit_axioms_strict FNE.Three.stepL_setup
#audit_axioms_strict FNE.Three.levels_inv
#audit_axioms_strict FNE.Three.LevelInv.setup
#audit_axioms_strict FNE.Three.levels_top
#audit_axioms_strict FNE.Three.levels_family_ac
#audit_axioms_strict FNE.Three.levels_letters
#audit_axioms_strict FNE.Three.thin_base
#audit_axioms_strict FNE.Three.levels_singleton

-- Section 9.3: list-family cores of thr:promote and thr:word (session 7)
#audit_axioms_strict FNE.Three.promote_lists
#audit_axioms_strict FNE.Three.word_lists

-- Section 7.1: (Q1)-(Q3) for R_M (session 8)
#audit_axioms_strict FNE.Three.mem_RM
#audit_axioms_strict FNE.Three.FTile.toTile_injective
#audit_axioms_strict FNE.Three.ofTile_spec
#audit_axioms_strict FNE.Three.tpar_inA
#audit_axioms_strict FNE.Three.Q1_E
#audit_axioms_strict FNE.Three.Q1_N
#audit_axioms_strict FNE.Three.Q2_E
#audit_axioms_strict FNE.Three.Q2_N
#audit_axioms_strict FNE.Three.Q2_rulesH
#audit_axioms_strict FNE.Three.Q2_rulesV
#audit_axioms_strict FNE.Three.Q3_E
#audit_axioms_strict FNE.Three.Q3_N
#audit_axioms_strict FNE.Three.Q3_palette
#audit_axioms_strict FNE.Three.cls_E
#audit_axioms_strict FNE.Three.cls_N
#audit_axioms_strict FNE.Three.quad_of_cls

-- Section 9.1: thr:move, thr:phase, pins, thr:lists (session 8)
#audit_axioms_strict FNE.Three.ctr_of_compatible
#audit_axioms_strict FNE.Three.ctr_match_e1
#audit_axioms_strict FNE.Three.ctr_match_e1'
#audit_axioms_strict FNE.Three.ctr_match_e2
#audit_axioms_strict FNE.Three.ctr_match_e2'
#audit_axioms_strict FNE.Three.cls_block
#audit_axioms_strict FNE.Three.thr_move
#audit_axioms_strict FNE.Three.walk_token
#audit_axioms_strict FNE.Three.thr_phase
#audit_axioms_strict FNE.Three.classPart_safe
#audit_axioms_strict FNE.Three.exists_classPart
#audit_axioms_strict FNE.Three.walker_move
#audit_axioms_strict FNE.Three.walker_total
#audit_axioms_strict FNE.Three.walker_pin1
#audit_axioms_strict FNE.Three.walker_pin2
#audit_axioms_strict FNE.Three.pin_clone_two
#audit_axioms_strict FNE.Three.pin_clone_one
#audit_axioms_strict FNE.Three.pin_clone_both
#audit_axioms_strict FNE.Three.quad_iota
#audit_axioms_strict FNE.Three.lists_family
#audit_axioms_strict FNE.Three.lists_ac
#audit_axioms_strict FNE.Three.lists_pin1
#audit_axioms_strict FNE.Three.lists_pin2

-- Section 9.3, token level: thr:start, thr:promote, thr:word (session 8)
#audit_axioms_strict FNE.Three.dyadicSetup_of
#audit_axioms_strict FNE.Three.thr_start
#audit_axioms_strict FNE.Three.thr_promote
#audit_axioms_strict FNE.Three.thr_word
#audit_axioms_strict FNE.Three.exists_cornerPair

-- Section 9.4: thr:quarters, thr:roles, thr:meet, thm:three from (Q5) (session 8)
#audit_axioms_strict FNE.Three.quad_cell
#audit_axioms_strict FNE.Three.cell_par
#audit_axioms_strict FNE.Three.WordSetup.quarters
#audit_axioms_strict FNE.Three.WordSetup.walk_right
#audit_axioms_strict FNE.Three.WordSetup.walk_left
#audit_axioms_strict FNE.Three.WordSetup.walk_up
#audit_axioms_strict FNE.Three.WordSetup.walk_down
#audit_axioms_strict FNE.Three.corridor
#audit_axioms_strict FNE.Three.WordSetup.roles_h
#audit_axioms_strict FNE.Three.WordSetup.roles_v
#audit_axioms_strict FNE.Three.payInf_mem
#audit_axioms_strict FNE.Three.payInf_EW
#audit_axioms_strict FNE.Three.payInf_NS
#audit_axioms_strict FNE.Three.meet_E
#audit_axioms_strict FNE.Three.meet_N
#audit_axioms_strict FNE.Three.exists_enum
#audit_axioms_strict FNE.Three.Pal_meet
#audit_axioms_strict FNE.Three.WordSetup.pal_of_walker
#audit_axioms_strict FNE.Three.WordSetup.pal_mv
#audit_axioms_strict FNE.Three.WordSetup.row_chain
#audit_axioms_strict FNE.Three.WordSetup.col_chain
#audit_axioms_strict FNE.Three.three_of_board

-- Section 6.5: prop:board, (Q5); thm:three; Theorem C and cor:eight up to computability (session 8)
#audit_axioms_strict FNE.Three.leftEnd_in_J
#audit_axioms_strict FNE.Three.rightEnd_in_J
#audit_axioms_strict FNE.Three.exists_rank_zero
#audit_axioms_strict FNE.Three.wordTower_rel
#audit_axioms_strict FNE.Three.sigmaPow_inA
#audit_axioms_strict FNE.Three.word_vwall
#audit_axioms_strict FNE.Three.word_hwall
#audit_axioms_strict FNE.Three.line_nowall
#audit_axioms_strict FNE.Three.line_corridor
#audit_axioms_strict FNE.Three.resSet_spec
#audit_axioms_strict FNE.Three.card_resSet
#audit_axioms_strict FNE.Three.bFree_two_bD_add
#audit_axioms_strict FNE.Three.many_free
#audit_axioms_strict FNE.Three.word_seed
#audit_axioms_strict FNE.Three.board
#audit_axioms_strict FNE.Three.three_tokens
#audit_axioms_strict FNE.Three.theoremC_familyR
#audit_axioms_strict FNE.Three.eight_familyR
#audit_axioms_strict FNE.Three.cor_eight_of_computable

-- Section 8: computability of `M ↦ R_M` (session 9)
#audit_axioms_strict FNE.Family.colCode_injective
#audit_axioms_strict FNE.Family.colCodeL_eq
#audit_axioms_strict FNE.Family.payList_eq
#audit_axioms_strict FNE.Family.seedTile_indep
#audit_axioms_strict FNE.Family.tileOf_congr
#audit_axioms_strict FNE.Family.SatAt.congr_box
#audit_axioms_strict FNE.Family.satAt_iff
#audit_axioms_strict FNE.Family.sat_iff
#audit_axioms_strict FNE.Family.tileOf_lists
#audit_axioms_strict FNE.Family.inT_iff
#audit_axioms_strict FNE.Family.palette_iff
#audit_axioms_strict FNE.Family.familyR_eq
#audit_axioms_strict FNE.Family.primrec_sublists
#audit_axioms_strict FNE.Family.primrec_oTr
#audit_axioms_strict FNE.Family.primrec_next
#audit_axioms_strict FNE.Family.primrec_quads
#audit_axioms_strict FNE.Family.primrecPred_actChk
#audit_axioms_strict FNE.Family.primrec_familyR
#audit_axioms_strict FNE.Family.computable_familyR

-- D1 bridge: the reductions around the compiler (session 9)
#audit_axioms_strict FNE.not_computable_ergodic_of
#audit_axioms_strict FNE.not_computable_ergodic
#audit_axioms_strict FNE.not_computable_halts_of_compiler
#audit_axioms_strict FNE.cor_eight_undecidable_of_compiler

-- D1 compiler (session 10): `Compiler/TM0.lean`
#audit_axioms_strict FNE.Compiler.lookup_eq_some
#audit_axioms_strict FNE.Compiler.symNum_default
#audit_axioms_strict FNE.Compiler.symNum_injective
#audit_axioms_strict FNE.Compiler.stIdx_inj
#audit_axioms_strict FNE.Compiler.lookup_state
#audit_axioms_strict FNE.Compiler.lookup_pre
#audit_axioms_strict FNE.Compiler.step_rel
#audit_axioms_strict FNE.Compiler.step_halt
#audit_axioms_strict FNE.Compiler.reaches_rel
#audit_axioms_strict FNE.Compiler.prefix_run
#audit_axioms_strict FNE.Compiler.prefix_done
#audit_axioms_strict FNE.Compiler.mk₁_nth
#audit_axioms_strict FNE.Compiler.rel_init
#audit_axioms_strict FNE.Compiler.compile_halts
#audit_axioms_strict FNE.Compiler.primrec_pre
#audit_axioms_strict FNE.Compiler.primrec_mkMachine

-- D1 compiler (session 10): `Compiler/Universal.lean`
#audit_axioms_strict FNE.Compiler.bin_eq
#audit_axioms_strict FNE.Compiler.trNat_eq
#audit_axioms_strict FNE.Compiler.primrec_bin
#audit_axioms_strict FNE.Compiler.univFun_partrec
#audit_axioms_strict FNE.Compiler.univCode_eval
#audit_axioms_strict FNE.Compiler.supports₀
#audit_axioms_strict FNE.Compiler.init_eq
#audit_axioms_strict FNE.Compiler.eval_dom
#audit_axioms_strict FNE.Compiler.compiler_halts
#audit_axioms_strict FNE.Compiler.input_map
#audit_axioms_strict FNE.Compiler.primrec_compiler
#audit_axioms_strict FNE.Compiler.computable_compiler
