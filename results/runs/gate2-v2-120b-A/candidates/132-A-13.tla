---------------- MODULE MCMajority ----------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound, Seq

VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Bounded sequence generator: Seq is the set of all finite sequences over
\* the value set {A, B, C} whose length is at most the constant 'bound'.
\* We define it here to match the expected constant but also keep a local
\* definition for convenience.
\* ----------------------------------------------------------------------
SeqSet == { s \in Seq : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* Initialization: choose any bounded sequence and any initial candidate,
\* start scanning at position 1 with counter 0.
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in SeqSet
    /\ pos = 1
    /\ cand \in {A, B, C}
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Scanning actions.
\*   * If the counter is 0, we adopt the current element as the new candidate
\*     and reset the counter to 1.
\*   * If the current element equals the candidate, we increment the counter.
\*   * Otherwise we decrement the counter.
\*   * When the end of the sequence is reached (pos = Len(seq) + 1) we
\*     stay in the same state (no further progress).
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET cur == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = cur
              /\ cnt' = 1
          ELSE IF cur = cand THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ seq' = seq
    \/ /\ pos = Len(seq) + 1
       /\ UNCHANGED << seq, pos, cand, cnt >>

\* ----------------------------------------------------------------------
\* The full specification: weak fairness on the Next action.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>> WF_<<seq, pos, cand, cnt>> (Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant.
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in SeqSet
    /\ pos \in Nat
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Correctness invariant: after a complete scan (pos = Len(seq) + 1),
\* if there exists a strict majority element in seq, then that element must
\* equal the candidate.
\* ----------------------------------------------------------------------
MajCounts(e) == Cardinality({ i \in 1..Len(seq) : seq[i] = e })
Correct ==
    (pos = Len(seq) + 1) =>
        ( \E e \in {A, B, C} :
            (MajCounts(e) > Len(seq) / 2) /\ cand = e)

\* ----------------------------------------------------------------------
\* Inductive invariant (the same set as required by the configuration).
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Correct

\* ----------------------------------------------------------------------
\* Expose the identifiers required by the .cfg.
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv

====