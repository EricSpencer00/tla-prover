---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* This module models the configuration infrastructure for TLAPS.
\* It defines backend pragma operators and fundamental temporal logic
\* proof rules, together with placeholder state variables and actions.
\* ----------------------------------------------------------------------

CONSTANTS BackendPragmas, ExtensPragma, FinitePragma,
          Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4,
          InvarianceRule, WFRule, SFRule, WFImplySF,
          Invariance, WF, SF

VARIABLES x, y, z, aux

\* ----------------------------------------------------------------------
\* Initial state (no specific constraints required by the description)
\* ----------------------------------------------------------------------
Init ==
    /\ x \in Nat
    /\ y \in Nat
    /\ z \in Nat
    /\ aux = {}

\* ----------------------------------------------------------------------
\* Placeholder actions (the description does not prescribe any)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ x' = x + 1
         /\ y' = y
         /\ z' = z
         /\ aux' = aux
    \/ /\ x' = x
         /\ y' = y + 1
         /\ z' = z
         /\ aux' = aux
    \/ /\ x' = x
         /\ y' = y
         /\ z' = z + 1
         /\ aux' = aux

\* ----------------------------------------------------------------------
\* Proof system backend pragmas (as constant definitions)
\* ----------------------------------------------------------------------
BackendPragmas ==
    [ Zenon     |-> "zenon",
      Isabelle  |-> "isabelle",
      CVC3      |-> "cvc3",
      Yices     |-> "yices",
      VeriT     |-> "verit",
      Z3        |-> "z3",
      SPASS     |-> "spass",
      LS4       |-> "ls4" ]

ExtensPragma  == "extensionality"
FinitePragma  == "finite"

\* ----------------------------------------------------------------------
\* Temporal logic proof rules (represented as constant identifiers)
\* ----------------------------------------------------------------------
InvarianceRule == "Invariance"
WFRule          == "WeakFairness"
SFRule          == "StrongFairness"
WFImplySF       == "WFImplySF"

\* ----------------------------------------------------------------------
\* Operators that expose the rule names for use in proofs
\* ----------------------------------------------------------------------
Invariance == InvarianceRule
WF         == WFRule
SF         == SFRule

\* ----------------------------------------------------------------------
\* Specification components required by TLC
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<x, y, z, aux>>

INIT == Init
NEXT == Next

\* ----------------------------------------------------------------------
\* Safety invariants derived from the description
\*   1. Set extensionality (as a theorem, not a state invariant)
\*   2. No set contains every possible value (again as a theorem)
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A S, T \in SUBSET Nat :
        (\A v \in Nat : (v \in S) <=> (v \in T)) => S = T

NoUniversalSet ==
    \A S \in SUBSET Nat : ~(\A v \in Nat : v \in S)

\* The .cfg does not require explicit INVARIANTS or PROPERTIES,
\* but they are provided for completeness.
INVARIANTS == <<>>
PROPERTIES == <<>>

=============================================================================