---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  ZenonTimeout, YicesTimeout, Z3Timeout, ConstTrue, ConstFalse

VARIABLES
  ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled
  VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled

vars == <<ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled,
          VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled>>

TypeOK ==
  /\ ZenonEnabled \in BOOLEAN /\ IsabelleEnabled \in BOOLEAN
  /\ CVC3Enabled \in BOOLEAN /\ YicesEnabled \in BOOLEAN
  /\ VeriTEnabled \in BOOLEAN /\ Z3Enabled \in BOOLEAN
  /\ SPASSenabled \in BOOLEAN /\ LS4enabled \in BOOLEAN

Init ==
  /\ ZenonEnabled = FALSE /\ IsabelleEnabled = FALSE
  /\ CVC3Enabled = FALSE /\ YicesEnabled = FALSE
  /\ VeriTEnabled = FALSE /\ Z3Enabled = FALSE
  /\ SPASSenabled = FALSE /\ LS4enabled = FALSE

DispatchZenon ==
  /\ ~ZenonEnabled /\ ZenonEnabled' = TRUE
  /\ UNCHANGED <<IsabelleEnabled, CVC3Enabled, YicesEnabled,
                VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled>>

DispatchIsabelle ==
  /\ ~IsabelleEnabled /\ IsabelleEnabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, CVC3Enabled, YicesEnabled,
                VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled>>

DispatchCVC3 ==
  /\ ~CVC3Enabled /\ CVC3Enabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, YicesEnabled,
                VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled>>

DispatchYices ==
  /\ ~YicesEnabled /\ YicesEnabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, CVC3Enabled,
                VeriTEnabled, Z3Enabled, SPASSenabled, LS4enabled>>

DispatchVeriT ==
  /\ ~VeriTEnabled /\ VeriTEnabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled,
                Z3Enabled, SPASSenabled, LS4enabled>>

DispatchZ3 ==
  /\ ~Z3Enabled /\ Z3Enabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled,
                VeriTEnabled, SPASSenabled, LS4enabled>>

DispatchSPASS ==
  /\ ~SPASSenabled /\ SPASSenabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled,
                VeriTEnabled, Z3Enabled, LS4enabled>>

DispatchLS4 ==
  /\ ~LS4enabled /\ LS4enabled' = TRUE
  /\ UNCHANGED <<ZenonEnabled, IsabelleEnabled, CVC3Enabled, YicesEnabled,
                VeriTEnabled, Z3Enabled, SPASSenabled>>

Next ==
  \/ DispatchZenon \/ DispatchIsabelle \/ DispatchCVC3 \/ DispatchYices
  \/ DispatchVeriT \/ DispatchZ3 \/ DispatchSPASS \/ DispatchLS4

Spec == Init /\ [][Next]_vars

ExtensionalEquality ==
  \A S, T \in SUBSET 0..3 : (S = T) <=> (\A x \in 0..3 : (x \in S) <=> (x \in T))

NoUniversalSet ==
  \A S \in SUBSET 0..3 : S # 0..3

TemporalLogicRules ==
  /\ \A S \in SUBSET 0..3 : ExtensionalEquality
  /\ \A S \in SUBSET 0..3 : NoUniversalSet

====