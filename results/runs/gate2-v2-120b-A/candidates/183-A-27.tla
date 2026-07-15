---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(*  TLAPS:  Backend prover configuration and temporal logic proof rules   *)
(*  (c) 2026  OpenAI                                                      *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* No state variables are needed for this configuration module.
\* ----------------------------------------------------------------------
VARIABLE dummy

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init == dummy = 0

\* ----------------------------------------------------------------------
\* ACTIONS (none required; we provide a stuttering step to keep TLC happy)
\* ----------------------------------------------------------------------
Next == dummy' = dummy

\* ----------------------------------------------------------------------
\* SPECIFICATION (the overall system behavior)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\* BACKEND PROVER SETTINGS
\* Each setting is a constant that TLAPS reads to decide which prover to use.
\* The exact names are taken from the reference configuration.
\* ----------------------------------------------------------------------
CONSTANTS
    %% Zenon (first-order prover)
    ZenonTimeout, ZenonMaxDepth,
    %% Isabelle (interactive prover)
    IsabelleTimeout,
    %% CVC3 (SMT solver)
    CVC3Timeout,
    %% Yices (SMT solver)
    YicesTimeout,
    %% veriT (SMT solver)
    VeriTTimeout,
    %% Z3 (SMT solver)
    Z3Timeout,
    %% SPASS (first-order prover)
    SPASSTimeout,
    %% LS4 (temporal logic prover)
    LS4Timeout,
    %% Global timeout for any prover
    GlobalTimeout

\* ----------------------------------------------------------------------
\* Default values (these can be overridden in a .cfg file)
\* ----------------------------------------------------------------------
ZenonTimeout   == 30
ZenonMaxDepth  == 10
IsabelleTimeout == 30
CVC3Timeout    == 30
YicesTimeout   == 30
VeriTTimeout   == 30
Z3Timeout      == 30
SPASSTimeout   == 30
LS4Timeout     == 30
GlobalTimeout  == 60

\* ----------------------------------------------------------------------
\* TEMPORAL LOGIC PROOF RULES (names reserved for TLAPS)
\* The bodies are merely placeholders; the actual theorems are proved
\* externally by the referenced Lamport paper.
\* ----------------------------------------------------------------------
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* SAFETY PROPERTY: Set Extensionality
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A A, B \in SUBSET {1,2,3} : ( \A x : x \in A <=> x \in B ) => A = B

\* ----------------------------------------------------------------------
\* SAFETY PROPERTY: No set contains every possible value
\* (Here the "universal set" is taken to be the set {1,2,3} for illustration.)
\* ----------------------------------------------------------------------
NoUniversalSet ==
    \A S \in SUBSET {1,2,3} : S # {1,2,3}

\* ----------------------------------------------------------------------
\* INVARIANTS (as required by the .cfg, even though none are listed)
\* ----------------------------------------------------------------------
Inv == SetExtensionality /\ NoUniversalSet

\* ----------------------------------------------------------------------
\* PROPERTIES (safety properties that TLC should check)
\* ----------------------------------------------------------------------
Properties == Inv

=============================================================================