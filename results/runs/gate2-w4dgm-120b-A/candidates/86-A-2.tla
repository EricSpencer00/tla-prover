---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

\* Backend pragmas: each instructs TLAPS to use that prover for the current
\* proof obligation and carries a time budget (0 = default/unspecified).
\* The fairness rules below are the ones from Lamport's TLA+ paper.
Pragmas == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* A pragmata record is the set of backends selected for one step of the proof,
\* together with an auxiliary budget field that is otherwise unused (still).
PragmaRecord == [p: SUBSET Pragmas, budget: Nat]

NoPragma == [p |-> {}, budget |-> 0]

\* A single-step proof commitment may name any non-empty set of backends; the
\* budget field is a leftover from earlier drafts and is never constrained.
Commitments == {NoPragma} \cup [p \in SUBSET Pragmas : p # {}, budget \in 0..2]

VARIABLES history

vars == <<history>>

Init == history = {NoPragma}

\* An engineer may retry a proof step with a different (or the same) set of
\* backends and a different budget, so the space of reachable histories is
\* highly connected and every pair of reachable states is reachable in two
\* steps via an intermediate state.
AddStep(h) ==
  /\ h \in Commitments
  /\ history' = history \cup {h}

\* Because proofs can also be torn down (a step is abandoned) and redone
\* repeatedly, the history never only grows -- the set of commitments already
\* applied can shrink back down to the empty starting point.
RemoveStep(h) ==
  /\ h \in history
  /\ history' = history \ {h}

Next == (\E h \in Commitments : AddStep(h)) \/ (\E h \in history : RemoveStep(h))

Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: at least one proof step using the LS4 temporal prover was
\* actually committed, so the configuration never loses the one prover that
\* takes care of step simulation entirely on its own.
LivenessStepPresent == \E r \in history : LS4 \in r.p

====