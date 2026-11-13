/- Exact types of every session-5 finished theorem and the three frozen targets. -/
import ForgettingLower

set_option autoImplicit false

#check @FLD.Coh.ul_down
#check @FLD.Coh.ul_move
#check @FLD.Coh.add_pair
#check @FLD.Coh.ul_reach
#check @FLD.Coh.ul_common
#check @FLD.Coh.ul_same
#check @FLD.Coh.ul_east
#check @FLD.Coh.ul_north
#check @FLD.Coh.tiles_of_UL
#check @FLD.Coh.live_marked
#check @FLD.Coh.extraction_ae
#check @FLD.Forget.disc_step
#check @FLD.Forget.disc_path
#check @FLD.Forget.unique_complete_all
#check @FLD.Forget.unique_complete
#check @FLD.Forget.ergodic_of_not_tiles
#check @FLD.Forget.flow_timeNoise
#check @FLD.Forget.complete_timeNoise
#check @FLD.Forget.all_time_singleton
#check @FLD.Forget.allTimeCFTP_of_not_tiles
#check @FLD.Memory.traj_succ
#check @FLD.Memory.clone_cover
#check @FLD.Memory.blank_cover
#check @FLD.Memory.marked_of_markedFrom
#check @FLD.Forget.root_encoding
#check @FLD.Forget.root_measure_le
#check @FLD.Forget.root_base_le
#check @FLD.Forget.root_tail_le
#check @FLD.Forget.root_bound
#check @FLD.Memory.dec_cloneCfg
#check @FLD.Memory.dec_blankCfg
#check @FLD.Memory.dec_siteEquiv
#check @FLD.Memory.law_bad_le
#check @FLD.Memory.memory_branch
#check @FLD.Memory.clone_blank_le
#check @FLD.Memory.blank_live_le
#check @FLD.Memory.twoInvariant_of_tiles
#check @FLD.z4_classification
#check @FLD.z4_machine_corollary
#check @FLD.z4_raw_undecidable

example : FLD.Z4Classification := FLD.z4_classification
example : FLD.Z4MachineCorollary := FLD.z4_machine_corollary
example : FLD.Z4RawUndecidable := FLD.z4_raw_undecidable

#print axioms FLD.z4_classification
#print axioms FLD.z4_machine_corollary
#print axioms FLD.z4_raw_undecidable
