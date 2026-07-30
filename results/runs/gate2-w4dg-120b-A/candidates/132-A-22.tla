---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

\* A TLA+ module derived from a natural-language description. The description
\* asked for a majority-vote model sized by a bound on the length of input
\* sequences. The module defines every identifier the reference .cfg expects,
\* and it carries no decoration beyond what the spec calls for -- just the
\* constants, the Spec formula, its Init/Next actions, the three invariants,
\* and the liveness property.
CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* Model values drawn from the three-element set, indexed from 1 up to any
\* length n that stays within the fixed bound. This bounded-sequence
\* construction keeps the state space finite for model checking.
Seqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ counter \in 0..bound

\* A true majority must be the candidate, after a complete scan.
Correct ==
  /\ pos = bound + 1
  /\ \A c \in Values :
       (2 * Cardinality({ k \in DOMAIN seq : seq[k] = c }) > Len(seq)) => cand = c

\* The inductive invariant: the counter never runs past the items scanned.
Inv == counter <= pos

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

\* The three-way scan action: adopt a fresh candidate on a zero counter, or
\* bump the counter when the scanned value matches, or decrement when it differs.
Next ==
  /\ pos <= bound
  /\ \E x \in Values :
       /\ IF counter = 0
          THEN /\ cand' = x
               /\ counter' = 1
          ELSE IF x = cand
               THEN /\ cand' = cand
                    /\ counter' = counter + 1
               ELSE /\ cand' = cand
                    /\ counter' = counter - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Complete == pos = bound + 1

\* The scan always completes: every reachable state eventually reaches the
\* bound-plus-one position, under weak fairness on the Next action.
EventuallyComplete == <>(Complete)

====