---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
    Zenon,
    Isabelle,
    CVC3,
    Yices,
    VeriT,
    Z3,
    SPASS,
    LS4,
    MaxTimeout

ASSUME MaxTimeout \in Nat

\* Backend dispatching operators: each sends a proof obligation to the named prover
\* with the given timeout. The LS4 operator additionally takes a temporal tactic.
ProveWithZenon(f, t) == t <= MaxTimeout /\ Zenon
ProveWithIsabelle(f, t) == t <= MaxTimeout /\ Isabelle
ProveWithCVC3(f, t) == t <= MaxTimeout /\ CVC3
ProveWithYices(f, t) == t <= MaxTimeout /\ Yices
ProveWithVeriT(f, t) == t <= MaxTimeout /\ VeriT
ProveWithZ3(f, t) == t <= MaxTimeout /\ Z3
ProveWithSPASS(f, t) == t <= MaxTimeout /\ SPASS
ProveWithLS4(f, t, tac) == t <= MaxTimeout /\ LS4 /\ tac

\* Temporal logic proof rules from Lamport's TLA+ paper. These are not invoked
\* here; their presence reserves the names for future extensions.
InvarianceRule == TRUE
WellFormedStepRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE

\* Foundational theorems (safety props) about sets, always available.
Extensionality == TRUE
NoSetContainsAll == TRUE

Specification == Extensionality /\ NoSetContainsAll

Init == UNCHANGED Specification

Next == UNCHANGED Specification

SpecInit == Init
SpecNext == Next
SpecSpec == Specification
SpecInvars == {Extensionality, NoSetContainsAll}
SpecProps == {}

====