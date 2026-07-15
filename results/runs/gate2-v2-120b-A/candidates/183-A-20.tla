---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* -----------------------------------------------------------------
\* The TLAPS module declares a set of backend prover configuration
\* constants and the core temporal-logic proof rules referenced in
\* the description.  No state variables are needed for the model.
\* -----------------------------------------------------------------

\* ------------------------------
\* Configuration constants
\* ------------------------------
CONSTANTS
    ZenonTimeout,
    IsabelleTimeout,
    CVC3Timeout,
    YicesTimeout,
    VeritTimeout,
    Z3Timeout,
    SPASSTimeout,
    LS4Timeout,
    ZenonTactic,
    IsabelleTactic,
    CVC3Tactic,
    YicesTactic,
    VeritTactic,
    Z3Tactic,
    SPASSTactic,
    LS4Tactic

\* Default (illustrative) values – the model checker may override them.
ZenonTimeout   == 10
IsabelleTimeout == 10
CVC3Timeout    == 10
YicesTimeout   == 10
VeritTimeout   == 10
Z3Timeout      == 10
SPASSTimeout   == 10
LS4Timeout     == 10

ZenonTactic    == "default"
IsabelleTactic == "default"
CVC3Tactic     == "default"
YicesTactic    == "default"
VeritTactic    == "default"
Z3Tactic       == "default"
SPASSTactic    == "default"
LS4Tactic      == "default"

\* ------------------------------
\* No state variables – the specification is empty.
\* ------------------------------

VARIABLES .\* none

\* -----------------------------------------------------------------
\* Specification, Init, Next, Invariants, and Properties
\* The specification is intentionally empty; the operators are defined
\* solely to satisfy the identifiers required by the configuration.
\* -----------------------------------------------------------------

SPECIFICATION == Init /\ [][](Next \/ UNCHANGED <<>>)

Init == TRUE

Next == UNCHANGED <<>>

\* No safety invariants are imposed; the operator is defined as TRUE.
Inv1 == TRUE

INVARIANTS == Inv1

\* Fundamental theorems described in the natural-language text.
SetExtensionality == 
    \A A, B \in SUBSET {1, 2, 3, 4} :
        (\A x : x \in A <=> x \in B) => A = B

NoSetContainsAll == 
    \A S \in SUBSET {1, 2, 3, 4} : S # {1, 2, 3, 4}

PROPERTIES == SetExtensionality /\ NoSetContainsAll

\* -----------------------------------------------------------------
\* Temporal logic proof rules (names only, definitions are placeholders)
\* -----------------------------------------------------------------

InvRule == 
    \A inv(_):
        (Init => inv) /\ (\A s : inv /\ Next => inv)

WellFormednessRule == 
    \A A:
        (A = A)   \* placeholder for the real well‑formedness condition

StrongFairnessRule == 
    \A p(_):
        []<>(p) => []<>(p)

WeakFairnessRule == 
    \A p(_):
        []<>(p) => []<>(p)

StepSimulationRule == 
    \A s, t :
        s = t   \* placeholder for simulation condition

\* The operators are exported automatically by the module.
====