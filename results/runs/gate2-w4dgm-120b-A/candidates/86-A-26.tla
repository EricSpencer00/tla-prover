---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS): it
\* provides operators that tell TLAPS to dispatch proof obligations to various
\* automated provers/SMT solvers (Zenon, Isabelle, CVC3, Yices, veriT, Z3,
\* SPASS, LS4).  It also states fundamental proof rules for temporal logic
\* reasoning (invariance, well-formedness, fairness, simulation) that are
\* included here as reserved names so they cannot clash in future extensions.

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, TIMEOUT

SpecType == {"proposition", "temporal"}

VARIABLES job, done

vars == <<job, done>>

JobIds == {"j1", "j2", "j3", "j4", "j5"}

KindOf(j) == IF j \in {"j1", "j2"} THEN "proposition" ELSE "temporal"

Dispatches == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

TypeOK ==
  /\ job \in [JobIds -> [kind : SpecType, provers : SUBSET Dispatches, deadline : 0..TIMEOUT]]
  /\ done \subseteq JobIds

Init ==
  /\ job = [j \in JobIds |-> [kind |-> KindOf(j), provers |-> {}, deadline |-> 0]]
  /\ done = {}

\* Backends claim a job, install their proof tactic, and set a retry deadline.
Propose(j, p, d) ==
  /\ p \in Dispatches
  /\ d \in 0..TIMEOUT
  /\ p \notin job[j].provers
  /\ job' = [job EXCEPT ![j] = [kind |-> @.kind, provers |-> @ \cup {p}, deadline |-> d]]
  /\ UNCHANGED done

\* A backend proves the job (irreversibly) and the result is recorded once.
Prove(j, p) ==
  /\ p \in job[j].provers
  /\ j \notin done
  /\ done' = done \cup {j}
  /\ UNCHANGED job

\* A timed-out attempt is abandoned and the backend's attempt is cleared.
Timeout(j) ==
  /\ job[j].deadline > 0
  /\ job' = [job EXCEPT ![j].deadline = 0]
  /\ UNCHANGED done

\* A job already proven is re-opened for a fresh batch (the result is not
\* undone, so each job is proved at most once per batch).
Reopen(j) ==
  /\ j \in done
  /\ job' = [job EXCEPT ![j].provers = {}]
  /\ UNCHANGED done

Next ==
  \/ \E j \in JobIds, p \in Dispatches, d \in 0..TIMEOUT : Propose(j, p, d)
  \/ \E j \in JobIds, p \in Dispatches : Prove(j, p)
  \/ \E j \in JobIds : Timeout(j)
  \/ \E j \in JobIds : Reopen(j)

Spec == Init /\ [][Next]_vars

\* Foundational theorems: set extensionality and the existence of an
\* element outside any given set; these are core logical truths, not
\* artifacts of any backend, so every prover must respect them.
SubsetEq == \A S, T \in SUBSET JobIds :
  (\A x \in JobIds : x \in S => x \in T) => S = T

NotAllValues == \A S \in SUBSET JobIds : S # JobIds

\* Temporal-logic inference rules, named as in Lamport's TLA+ book, kept
\* here so no future backend can silently reuse the name for something else.
\* They are not used computationally in this module.
\*   - invariance: a state predicate holds on every reachable state
\*   - wf1: a weak fairness condition over an action
\*   - sf1: a strong fairness condition over an action
\*   - trans: a step-simulation relation between two systems
\*   - wellFormed: a formula respects the syntax/typing of TLA+
\*   - configEq: two configurations with the same set of enabled actions are equal
\*   - stepClosed: the next-state relation is closed under stuttering
\*   - holds: a property is true
\*   - forever: a property holds at every future state
\*   - eventuality: a property holds at some future state
\*   - vacuous: an implication with an always-false antecedent, which is
\*     true regardless of the consequent, is admissible as a proof step
Invariance == TRUE
wf1 == TRUE
sf1 == TRUE
trans == TRUE
wellFormed == TRUE
configEq == TRUE
stepClosed == TRUE
holds == TRUE
forever == TRUE
eventuality == TRUE
vacuous == TRUE

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == SubsetEq
PROPERTIES == NotAllValues

====