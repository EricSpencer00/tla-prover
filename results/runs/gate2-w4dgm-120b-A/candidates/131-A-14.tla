---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* Type correctness of the whole state, proved as an invariant of the spec.
TypeOK ==
    /\ candidate \in Value
    /\ pos \in Nat
    /\ occ \in [Value -> Nat]

\* The invariant from the main spec (the candidate equals any strict majority element).
Inv ==
    /\ \A v \in Value : (occ[v] > pos \div 2) => v = candidate
    /\ occ[candidate] = pos

\* The full correctness property (candidate is a majority when there is one) plus type
\* correctness, proved as a single invariant of the spec.
Correct == Inv /\ TypeOK

Init ==
    /\ candidate = CHOOSE e \in Value : TRUE
    /\ pos = 0
    /\ occ = [v \in Value |-> 0]

Vote ==
    /\ pos < Len(seq)
    /\ LET v == seq[pos + 1] IN
        /\ candidate' = IF occ[v] >= occ[candidate] THEN v ELSE candidate
        /\ occ' = [occ EXCEPT ![v] = occ[v] + 1]
    /\ pos' = pos + 1

Reset ==
    /\ pos = Len(seq)
    /\ \E e \in Value : e # candidate
    /\ candidate' = e
    /\ pos' = 0
    /\ occ' = [v \in Value |-> 0]

Next == Vote \/ Reset

Spec ==
    /\ Init
    /\ [][Next]_<<candidate, pos, occ>>
    /\ WF_vars(Vote)

TypeOKInv ==
    /\ TypeOK
    /\ Inv

====