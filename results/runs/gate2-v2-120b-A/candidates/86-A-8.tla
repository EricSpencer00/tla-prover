---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* This module captures the configuration infrastructure for TLAPS.
\* It defines operators that specify which backend provers to invoke.
\* No state variables are required for this configuration module.

\* ----------------------------------------------------------------------
\* Constants (no constants are required by the .cfg, but we declare a
\* placeholder to illustrate that the module may be extended.)
CONSTANTS

\* ----------------------------------------------------------------------
\* Backend prover configuration operators
\* Each operator returns a string that can be interpreted by TLAPS as an
\* instruction.  The exact syntax of the string is not enforced by this
\* module; it is provided for readability and future use.

Zenon      == "zenon"
Isabelle   == "isabelle"
CVC3       == "cvc3"
Yices      == "yices"
VeriT      == "verit"
Z3         == "z3"
SPASS      == "spass"
LS4        == "ls4"          \* LS4 temporal prover

\* Timeouts (in seconds) for each prover
ZenonTimeout      == 10
IsabelleTimeout   == 20
CVC3Timeout       == 15
YicesTimeout      == 15
VeriTTimeout      == 20
Z3Timeout         == 10
SPASSTimeout      == 30
LS4Timeout        == 15

\* Helper operator that builds a description of a prover invocation
ProverDesc(prover, timeout) ==
  <<prover, timeout>>

\* Exported operator that yields a set of all configured backend provers
ConfiguredProvers == {
    ProverDesc(Zenon, ZenonTimeout),
    ProverDesc(Isabelle, IsabelleTimeout),
    ProverDesc(CVC3, CVC3Timeout),
    ProverDesc(Yices, YicesTimeout),
    ProverDesc(VeriT, VeriTTimeout),
    ProverDesc(Z3, Z3Timeout),
    ProverDesc(SPASS, SPASSTimeout),
    ProverDesc(LS4, LS4Timeout)
  }

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rule placeholders.
\* The operators do not implement the rules; they merely reserve the names.
\* The body of each operator is TRUE, meaning the rule is assumed to hold.

InvarianceRule(p) == TRUE
WFRule(p)           == TRUE
SFRule(p)           == TRUE
StepSimulationRule == TRUE
WellFormednessRule == TRUE

\* ----------------------------------------------------------------------
\* SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES
\* The specification is trivial because the module does not model dynamic
\* state.  We define a dummy state variable to give meaning to the
\* temporal operators.

VARIABLE dummy

Init == dummy = 0

\* NEXT leaves the dummy variable unchanged; this yields a stuttering
\* behavior that satisfies all temporal operators without affecting the
\* configuration data.
Next == dummy' = dummy

\* The overall specification combines the initial predicate with the
\* stuttering step.
Spec == Init /\ [][Next]_<<dummy>>

\* INVARIANTS and PROPERTIES are defined as the sets of the two
\* foundational theorems mentioned in the description.

ExtensionalityTheorem ==
  \A A, B \in SUBSET Nat : (\A x : x \in A <=> x \in B) => A = B

NoUniversalSetTheorem ==
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

INVARIANTS == { ExtensionalityTheorem, NoUniversalSetTheorem }

PROPERTIES == {}

\* We expose the expected identifiers for the .cfg file.
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next

====