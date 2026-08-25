---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* This module provides configuration primitives for TLAPS and includes
\* foundational theorems about sets.  It also defines the standard
\* specification operators (SPECIFICATION, INIT, NEXT, INVARIANTS,
\* PROPERTIES) required by the reference configuration, even though the
\* system described has no state.
\* ----------------------------------------------------------------------

\* ----------- Constants --------------------------------------------------
CONSTANT UNIV

\* Assume UNIV is the universe of discourse (here we equate it with Nat)
ASSUME UNIV = Nat

\* ----------- Variables (none required; we introduce a dummy) -----------
VARIABLE dummy

\* ----------- Initial predicate -----------------------------------------
INIT == TRUE

\* ----------- Next-state relation ---------------------------------------
NEXT == UNCHANGED dummy

\* ----------- Specification ---------------------------------------------
SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

\* ----------- Invariants and Properties (empty sets) --------------------
INVARIANTS == {}

PROPERTIES == {}

\* ----------- Fundamental set theorems ---------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET UNIV : ~(\A x \in UNIV : x \in S)

\* ----------- Reserved temporal‑logic proof rule names ------------------
\* The following operators are declared only to reserve their names.
\* Their definitions are placeholders; actual proof rules are provided
\* by the TLAPS library.

Inv(_)== TRUE
WF(_,_)== TRUE
SF(_,_)== TRUE
StrongFair(_)== TRUE
WeakFair(_)== TRUE
StepSimulation(_,_)== TRUE

====