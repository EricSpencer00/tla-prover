(* automatically generated -- do not edit manually *)
theory tlapm_9ce20a imports Constant Zenon begin
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

(* Generated from file "./23_toy_consensus_epr.tla", line 74, characters 53-59 *)
lemma ob'1: (* 0b8d5aa3a9d559bccf7e3673dda8de24 *)
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_MapThenFoldSet_ suppressed *)
(* usable definition CONSTANT_Restrict_ suppressed *)
(* usable definition CONSTANT_RestrictDomain_ suppressed *)
(* usable definition CONSTANT_RestrictValues_ suppressed *)
(* usable definition CONSTANT_IsRestriction_ suppressed *)
(* usable definition CONSTANT_Range_ suppressed *)
(* usable definition CONSTANT_Pointwise_ suppressed *)
(* usable definition CONSTANT_Inverse_ suppressed *)
(* usable definition CONSTANT_AntiFunction_ suppressed *)
(* usable definition CONSTANT_IsInjective_ suppressed *)
(* usable definition CONSTANT_Injection_ suppressed *)
(* usable definition CONSTANT_Surjection_ suppressed *)
(* usable definition CONSTANT_Bijection_ suppressed *)
(* usable definition CONSTANT_ExistsInjection_ suppressed *)
(* usable definition CONSTANT_ExistsSurjection_ suppressed *)
(* usable definition CONSTANT_ExistsBijection_ suppressed *)
(* usable definition CONSTANT_FoldFunctionOnSet_ suppressed *)
(* usable definition CONSTANT_FoldFunction_ suppressed *)
(* usable definition CONSTANT_SumFunctionOnSet_ suppressed *)
(* usable definition CONSTANT_SumFunction_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_IsTransitivelyClosedOn_ suppressed *)
(* usable definition CONSTANT_IsWellFoundedOn_ suppressed *)
(* usable definition CONSTANT_SetLessThan_ suppressed *)
(* usable definition CONSTANT_WFDefOn_ suppressed *)
(* usable definition CONSTANT_OpDefinesFcn_ suppressed *)
(* usable definition CONSTANT_WFInductiveDefines_ suppressed *)
(* usable definition CONSTANT_WFInductiveUnique_ suppressed *)
(* usable definition CONSTANT_TransitiveClosureOn_ suppressed *)
(* usable definition CONSTANT_OpToRel_ suppressed *)
(* usable definition CONSTANT_PreImage_ suppressed *)
(* usable definition CONSTANT_LexPairOrdering_ suppressed *)
(* usable definition CONSTANT_LexProductOrdering_ suppressed *)
(* usable definition CONSTANT_FiniteSubsetsOf_ suppressed *)
(* usable definition CONSTANT_StrictSubsetOrdering_ suppressed *)
fixes a_CONSTANTunde_Nodeunde_a
fixes a_CONSTANTunde_Quorumunde_a
fixes a_CONSTANTunde_Valueunde_a
fixes a_VARIABLEunde_votedunde_a a_VARIABLEunde_votedunde_a'
fixes a_VARIABLEunde_voteunde_a a_VARIABLEunde_voteunde_a'
fixes a_VARIABLEunde_decidedunde_a a_VARIABLEunde_decidedunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_ChosenAt_ suppressed *)
(* usable definition ACTION_CastVote_ suppressed *)
(* usable definition ACTION_Decide_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition STATE_NextUnchanged_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Safety_ suppressed *)
(* usable definition CONSTANT_Symmetry_ suppressed *)
(* usable definition STATE_Inv220_1_0_def_ suppressed *)
(* usable definition STATE_Inv155_1_1_def_ suppressed *)
(* usable definition STATE_Inv201_2_2_def_ suppressed *)
(* usable definition STATE_IndAuto_ suppressed *)
shows "(((((a_STATEunde_IndAutounde_a) \<and> (a_ACTIONunde_Nextunde_a))) \<Rightarrow> ((a_h325d8a :: c))))"(is "PROP ?ob'1")
proof -
show "PROP ?ob'1"
by auto
qed
end
