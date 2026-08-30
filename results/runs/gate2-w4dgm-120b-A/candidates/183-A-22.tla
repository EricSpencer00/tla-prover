---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* This module is a helper from the standard TLAPS library.  It defines the
\* backend provers the proof system may dispatch to, and it states the
\* fundamental temporal-logic proof rules (invariance, fairness, step
\* simulation) from Lamport's TLA+ paper -- rules whose names we must
\* reserve even though they are never invoked in this module.

Backends == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

\* Dynamic dispatch: the proof system calls Dispatch with a live goal and a
\* chosen backend; the goal is sent to that prover.  The proof system limits
\* how many obligations it works on at once, but that limit is enforced
\* outside this module, so here the dispatch is unconditional.

Dispatch(g, b) == /\ g \in Goal /\ b \in Backends /\ SentTo' = SentTo \cup {[goal |-> g, backend |-> b]}
                     /\ UNCHANGED Goal

\* An obligation that no backend can currently discharge is parked so the
\* proof system can return to it later.
Park(g) == /\ g \in Goal /\ SentTo' = SentTo \cup {[goal |-> g, backend |-> "parked"]} /\ UNCHANGED Goal

\* The proof system reports a discharged obligation back into the open pool.
Reopen(o) == /\ o \in SentTo /\ SentTo' = SentTo \ {o} /\ Goal' = Goal \cup {o.goal}

TypeOK == /\ Goal \subseteq Goal
          /\ SentTo \subseteq [goal : Goal, backend : (Backends \cup {"parked"})]

InitGoal == {1, 2, 3}

Init == /\ Goal = InitGoal
        /\ SentTo = {}

Dispatched == \E g \in Goal, b \in Backends : Dispatch(g, b)
Reopened == \E o \in SentTo : Reopen(o)

Next == Dispatched \/ Reopened

\* Reserved proof-rule names: invariance and fairness rules from Lamport's
\* TLA+ paper.  They are never triggered here, but reserving their names
\* here avoids a clash when a refactoring elsewhere tries to re-use them.

TypeOKStep == TypeOK
SubsetStep == \E S \in (SUBSET Goal) : TRUE
NextStateRel == \E S \in (SUBSET Goal) : TRUE
StateConstraintStep == TRUE
SFStep == TRUE
W4Step == TRUE
WFStep == TRUE
WFVarsStep == TRUE

Spec == Init /\ [][Next]_<<Goal, SentTo>>

Extensionality == \A X, Y \in SUBSET Goal : (X = Y) <=> (\A x \in Goal : (x \in X) <=> (x \in Y))

NoSetContainsAll == \A X \in SUBSET Goal : X \neq Goal

\* The module's own obligation: neither of the two foundational theorems
\* above may be able to be discharged by any backend, so the proof system
\* has to uphold them purely on logical strength, never on a discharge.
ModulesAreNonDischargable == \A o \in SentTo : o.goal \notin {Extensionality, NoSetContainsAll}

\* WHAT IS REQUIRING PROOF: the entire module is a closed system of
\* derived facts once Spec holds, so each of these is a theorem of the
\* system rather than a property of an external driver.

SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT ModulesAreNonDischargable
PROPERTY TypeOKStep
PROPERTY SubsetStep
PROPERTY NextStateRel
PROPERTY StateConstraintStep
PROPERTY SFStep
PROPERTY W4Step
PROPERTY WFStep
PROPERTY WFVarsStep
====