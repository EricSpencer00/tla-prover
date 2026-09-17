(* automatically generated -- do not edit manually *)
theory tlapm_d588cf imports Constant Zenon begin
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

(* Generated from file "./2_TCommit.tla", line 71, characters 53-59 *)
lemma ob'1: (* 0b8d5aa3a9d559bccf7e3673dda8de24 *)
fixes a_CONSTANTunde_RMunde_a
fixes a_VARIABLEunde_rmStateunde_a a_VARIABLEunde_rmStateunde_a'
(* usable definition STATE_TCTypeOK_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition STATE_canCommit_ suppressed *)
(* usable definition STATE_notCommitted_ suppressed *)
(* usable definition ACTION_Prepare_ suppressed *)
(* usable definition ACTION_Decide_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_TCSpec_ suppressed *)
(* usable definition STATE_TCConsistent_ suppressed *)
(* usable definition CONSTANT_Symmetry_ suppressed *)
(* usable definition STATE_IndAuto_ suppressed *)
shows "(((((a_STATEunde_IndAutounde_a) \<and> (a_ACTIONunde_Nextunde_a))) \<Rightarrow> ((a_h325d8a :: c))))"(is "PROP ?ob'1")
proof -
show "PROP ?ob'1"
by auto
qed
end
