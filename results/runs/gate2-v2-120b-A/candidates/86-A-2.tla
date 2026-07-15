---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  This module provides backend pragmas for TLAPS, describing which     *)
(*  provers to use and defining basic temporal logic proof rules.        *)
(*  It also states two fundamental theorems about set extensionality and *)
(*  the non‑existence of a universal set.                                 *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Backend prover configuration
\* ----------------------------------------------------------------------
VARIABLES proved

\* No state variables are needed for the configuration itself. The
\* variable 'proved' is used only to force some non‑trivial action so that
\* the spec has a non‑empty NEXT relation.  Its concrete value is irrelevant.
proved == TRUE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ proved = TRUE

\* ----------------------------------------------------------------------
\* Next-state relation (a dummy no‑op step)
\* ----------------------------------------------------------------------
Next ==
    /\ proved' = proved

\* ----------------------------------------------------------------------
\* Specification (behaviour)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<proved>>

\* ----------------------------------------------------------------------
\* Backend provers (these are simply names; they are not used in the model)
\* ----------------------------------------------------------------------
Zenon   == "Zenon"
Isabelle == "Isabelle"
CVC3    == "CVC3"
Yices   == "Yices"
VeriT   == "veriT"
Z3      == "Z3"
SPASS   == "SPASS"
LS4     == "LS4"

\* ----------------------------------------------------------------------
\* Proof rules for temporal logic (names only, no implementation)
\* ----------------------------------------------------------------------
TemporalInvariant ==
    \A S, S' : (S = S') => (S \subseteq S')
TemporalWF ==
    \A S : []<>S   \* weak fairness placeholder
TemporalSF ==
    \A S : []S     \* strong fairness placeholder
TemporalStepSim ==
    \A S, S' : (S' = S) => [] (S = S')   \* step simulation placeholder

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A A, B \in SUBSET Nat :
        (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet ==
    \A S \in SUBSET Nat : \E x \in Nat : x \notin S

\* ----------------------------------------------------------------------
\* The specification, initial predicate, next-state relation, and theorems
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANTS    == SetExtensionality
PROPERTIES    == NoUniversalSet

(***************************************************************************)
(*  The identifiers SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES*)
(*  are required by the .cfg file.                                         *)
(***************************************************************************)

====