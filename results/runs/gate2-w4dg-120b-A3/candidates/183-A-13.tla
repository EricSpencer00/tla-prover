---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS),
\* mapping proof obligations to various automated provers/SMT solvers.
\* It also states two set-theoretic theorems (extensionality, and that no set
\* contains every value). The temporal-logic proof rules are included as
\* reserved names so they cannot clash with future extensions.

NoSolver == "none"

\* Dispatch operators: each takes a leaf obligation name and a timeout, and
\* returns the (solver, timeout) pair that TLAPS will fire on.
Zenon(leaf, timeout) == <<"Zenon", timeout>>
Isabelle(leaf, timeout) == <<"Isabelle", timeout>>
Yices(leaf, timeout) == <<"Yices", timeout>>
CVC3(leaf, timeout) == <<"CVC3", timeout>>
VeriT(leaf, timeout) == <<"VeriT", timeout>>
Z3(leaf, timeout) == <<"Z3", timeout>>
Spass(leaf, timeout) == <<"Spass", timeout>>
LS4(leaf, timeout) == <<"LS4", timeout>>

\* The module's "state" is the record of every dispatched leaf, and the
\* record's domain is the set of leaves that have actually been dispatched.
State == [leaf : IsFiniteSet => NoSolver \cup {<<"Zenon", 0>>}]

\* Every leaf must be dispatched at least once, and each dispatch records the
\* exact solver and timeout the leaf was sent to.
Dispatched == \A l \in {l \in Nat : l >= 1} : State[l] # NoSolver

\* Foundational set-theoretic theorems, always available in every model.
SETEXTENSIONALITY ==
    \A S, T \in {x \in Nat : x >= 1} :
        (\A y \in Nat : y \in S <=> y \in T) => S = T

NOSETCONTAINSALL ==
    \A S \in {x \in Nat : x >= 1} :
        (\A y \in Nat : y \in S) => FALSE

\* all of the model's assertions: the dispatch invariant plus the two set
\* theorems. No .cfg file can name a theorem that does not exist here.
SPECIFICATION == Dispatched /\ SETEXTENSIONALITY /\ NOSETCONTAINSALL

Init == TRUE
Next == TRUE
INVARIANTS == {}
PROPERTIES == {}

EXTENDED_CONST ==
    {SetOfNat, SetOfFin, SetOfInf, Nat, Leaf, LeafFinite, LeafInstable,
     WaitSet, ProcLeaf, ProcSet, ProcNow, ProcStep, ProcUnwritten}

\* The constant pool is the full set of identifiers this module ever
\* defines, so that the .cfg file's constant list can never hide one.
CONSTANTS == EXTENDED_CONST

====