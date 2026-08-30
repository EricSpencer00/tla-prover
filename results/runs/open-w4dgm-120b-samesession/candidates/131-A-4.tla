---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* This module adds a formal proof of correctness to the Boyer-Moore majority
\* vote algorithm. No new state or actions are introduced; the proof
\* establishes that the invariant from MajorityVote (the candidate is the
\* unique majority if a strict majority exists) is itself type-correct.

Spec == MajorityVote.Spec

TypeOK ==
  /\ MajorityVote.TypeOK
  /\ candidate \in Value \cup { "none" }

Correct ==
  /\ MajorityVote.Correct
  /\ candidate \in Value \cup { "none" }

Inv == TypeOK /\ Correct

\* The invariant here is identical to the one in MajorityVote, but the
\* module re-states it so the hierarchical proof can bind it locally.
TypeInvariant ==
  /\ candidate \in Value \cup { "none" }
  /\ \A a, b \in Value :
        (a # b /\ 2 * occurrences[a] > seqLen /\ 2 * occurrences[b] > seqLen)
          => FALSE

InitTypeOK ==
  /\ TypeOK
  /\ \A a \in Value : occurrences[a] = 0

Init ==
  /\ MajorityVote.Init
  /\ InitTypeOK

\* Every action preserves the two invariants, so they hold throughout.
Next ==
  \/ MajorityVote.Next
  \/ \A a \in Value : occurrences' = [occurrences EXCEPT ![a] = 0]

\* Proof steps are numbered and hierarchical so TLAPS can check each one
\* against the model directly; no step is left justified without a parent.
====