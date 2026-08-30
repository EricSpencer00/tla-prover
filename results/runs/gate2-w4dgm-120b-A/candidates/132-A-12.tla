---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

(* This module configures the Boyer-Moore majority vote specification with     *)
(* concrete model values and a bounded sequence length, so TLC can exhaustively  *)
(* explore the reachable state space.  The standard sequence operator Seq is     *)
(* replaced by a bounded, finite version (BoundedSeq) to keep the model finite.  *)

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

\* A bounded sequence: every function from 1..n to Values for some n <= bound.
BoundedSeq == { f \in [1..bound -> Values] : \A i \in 1..bound : i > Len(f) => f[i] = CHOOSE e \in Values : TRUE }

TypeOK ==
    /\ seq \in BoundedSeq
    /\ seq # <<>>
    /\ pos \in 1..bound
    /\ cand \in Values
    /\ count \in 0..bound

Init ==
    /\ \E s \in BoundedSeq :
        /\ seq = s
        /\ pos = Len(s) + 1
    /\ \E e \in Values : cand = e
    /\ count = 0

\* Scan the next element; three-way update of candidate, counter, and position.
Step ==
    /\ pos >= 2
    /\ LET x == seq[pos - 1] IN
        IF x = cand THEN count' = count + 1
        ELSE IF count = 0 THEN cand' = x /\ count' = 1
        ELSE count' = count - 1
    /\ pos' = pos - 1
    /\ UNCHANGED <<seq, cand>>

Next == Step

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Step) /\ WF_vars(Step) /\ WF_vars(Step)

(* Once the scan is complete, any element that appears more than half the    *)
(* time in the sequence must be the candidate the algorithm has settled on. *)
Correct ==
    /\ pos = 1
    /\ \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)) => e = cand

Inv ==
    /\ cand \in Values
    /\ count >= 0 /\ count <= Len(seq)

TypeOKp == TypeOK /\ Inv

StateSpace == {<<seq, pos, cand, count>> : Init /\ [][Next]_vars}

====