---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Configuration constants (time‑out values, tactic selections, …).  They are
\* deliberately left uninterpreted; the model checker will assign them
\* concrete values when a .cfg file is supplied.
\* ----------------------------------------------------------------------
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

\* ----------------------------------------------------------------------
\* No state variables are needed for this configuration module.
\* ----------------------------------------------------------------------
VARIABLES

\* ----------------------------------------------------------------------
\* SPECIFICATION, INIT, and NEXT are required identifiers that must be
\* present in every module that a TLC .cfg file may refer to.  Because the
\* natural‑language description does not define any dynamic behaviour, we
\* model a trivial system that stays in a single, empty state forever.
\* ----------------------------------------------------------------------
SPECIFICATION == TLAPSInit /\ []TLAPSNext
INIT == TLAPSInit
NEXT == TLAPSNext

\* The empty state – the only state this specification ever visits.
TLAPSInit == TRUE

\* Stutter step that leaves the (non‑existent) state unchanged.
TLAPSNext == UNCHANGED {}

\* ----------------------------------------------------------------------
\* INVARIANTS and PROPERTIES are also required identifiers.  They must be
\* defined, even though the description does not list concrete safety or
\* liveness properties.  We therefore expose the two foundational theorems
\* mentioned in the description as named invariants.
\* ----------------------------------------------------------------------
INVARIANTS == { Extensionality, NoUniversalSet }

\* PROPERTIES can be empty; we provide the same set as INVARIANTS so that a
\* .cfg file may reference either name without error.
PROPERTIES == INVARIANTS

\* ----------------------------------------------------------------------
\* Fundamental theorems (named invariants) -------------------------------------------------
\* 1. Set extensionality:
\*    Two sets that have exactly the same elements are equal.
\* 2. No universal set:
\*    There is no set that contains every possible value.
\* ----------------------------------------------------------------------
Extensionality ==
    \A X, Y \in SUBSET UNIV : (\A z : z \in X <=> z \in Y) => X = Y

NoUniversalSet ==
    \A S \in SUBSET UNIV : \E x : x \notin S

\* ----------------------------------------------------------------------
\* Backend‑selection operators – they merely expose the configured constants
\* so that a proof script can refer to them.  No operational effect is modelled.
\* ----------------------------------------------------------------------
Zenon == ZenonTimeout
Isabelle == IsabelleTimeout
CVC3 == CVC3Timeout
Yices == YicesTimeout
Verit == VeritTimeout
Z3 == Z3Timeout
SPASS == SPASSTimeout
LS4 == LS4Timeout

ZenonTac == ZenonTactic
IsabelleTac == IsabelleTactic
CVC3Tac == CVC3Tactic
YicesTac == YicesTactic
VeritTac == VeritTactic
Z3Tac == Z3Tactic
SPASSTac == SPASSTactic
LS4Tac == LS4Tactic

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders (names only; they do not affect
\* model checking).  Their presence reserves the identifiers for use by
\* external proofs.
\* ----------------------------------------------------------------------
InvarianceRule == TRUE
WFairnessRule == TRUE
SFairnessRule == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* Theorems that make the above placeholders visible to the model checker.
\* ----------------------------------------------------------------------
THEOREM InvarianceRuleIsTrue == InvarianceRule
THEOREM WFairnessRuleIsTrue == WFairnessRule
THEOREM SFairnessRuleIsTrue == SFairnessRule
THEOREM StepSimulationRuleIsTrue == StepSimulationRule

====