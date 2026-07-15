---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  This module provides configuration operators for the TLA+ Proof System*)
(*  (TLAPS). It defines backend provers, their options, and reserves the   *)
(*  names of fundamental temporal‑logic proof rules. The module does not *)
(*  model any state‑changing behavior; its purpose is to supply the       *)
(*  identifiers expected by the reference TLC configuration.              *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Backend prover configuration operators
\* ----------------------------------------------------------------------
Zenon == "Zenon"
Isabelle == "Isabelle"
CVC3 == "CVC3"
Yices == "Yices"
veriT == "veriT"
Z3 == "Z3"
SPASS == "SPASS"
LS4 == "LS4"

\* Timeout values (in seconds) for each prover – these are illustrative.
ZenonTimeout   == 10
IsabelleTimeout == 30
CVC3Timeout    == 20
YicesTimeout   == 15
veriTTimeout   == 20
Z3Timeout      == 15
SPASSTimeout   == 20
LS4Timeout     == 25

\* Options for each prover (expressed as arbitrary strings; they are not
\* interpreted by the specification itself but are available to the proof
\* system when the module is used as a backend configuration.)
ZenonOpts   == ""
IsabelleOpts == "-smt"
CVC3Opts    == ""
YicesOpts   == ""
veriTOpts   == ""
Z3Opts      == ""
SPASSOpts   == ""
LS4Opts     == ""

\* ----------------------------------------------------------------------
\* Reserved names for temporal‑logic proof rules (no definitions, only
\* stuttering to give them a value)
\* ----------------------------------------------------------------------
InvRule          == Stuttering
WFRule           == Stuttering
SFRule           == Stuttering
LivenessRule     == Stuttering
SimulationRule   == Stuttering
WellFormedRule   == Stuttering

\* ----------------------------------------------------------------------
\* Foundational theorems (provided as theorems so that they appear in the
\* module’s output but are not used in any model checking)
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV : (\A x \in UNIV : x \in S <=> x \in T) => S = T

THEOREM NoUniversalSet ==
  \A x \in UNIV : x \notin UNIV

\* ----------------------------------------------------------------------
\* The specification required by the task.  Because the original natural-
\* language description does not define any state variables, we model an
\* empty state using a dummy constant.
\* ----------------------------------------------------------------------
\* Dummy constant to give the specification a non‑empty set of variables
\* without introducing any behavior.
EmptyVar == 0

VARIABLES EmptyVar

\* Initial predicate – the dummy variable must equal its constant value.
Init == EmptyVar = 0

\* Next action – stutter (no state change) to keep the model simple.
Next == UNCHANGED EmptyVar

\* Specification operator required by the task.
Spec == Init /\ [][Next]_<<EmptyVar>>

\* The identifiers that the .cfg file expects.
SPEC    == Spec
INIT    == Init
NEXT    == Next
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====