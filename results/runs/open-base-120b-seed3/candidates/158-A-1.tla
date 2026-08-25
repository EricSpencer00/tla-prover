---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* operators used for model‑checking substitution *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

(* Initial state *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(* Safety predicate for a value at a given ballot *)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

(* Action: raise the promise threshold of an acceptor *)
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ votes'    = votes
    /\ threshold' = [threshold EXCEPT ![a] = b]

(* Action: an acceptor votes for a value in a ballot *)
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]
    /\ ~\E val \in Value : <<b, val>> \in votes[a]            \* not already voted in this ballot
    /\ \A a2 \in Acceptor : \A val2 \in Value :
          (<<b, val2>> \in votes[a2]) => val2 = v
    /\ Safe(b, v)
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

(* Next-state relation *)
Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

(* Specification *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Invariants *)

TypeCorrect ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> Int]
    /\ \A a \in Acceptor : \A <<b, val>> \in votes[a] :
          b \in Ballot /\ val \in Value

OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
              (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

AllVotesSafe ==
    \A a \in Acceptor : \A <<b, v>> \in votes[a] : Safe(b, v)

Inv == TypeCorrect /\ OneValuePerBallot /\ AllVotesSafe

(* --------------------------------------------------------------------- *)
(* Consistency property *)

Chosen(v) ==
    \E b \in Ballot : \E Q \in Quorum : \A a \in Q : <<b, v>> \in votes[a]

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(* --------------------------------------------------------------------- *)
(* Symmetry set for model checking *)

MCSymmetry == { [a \in Acceptor |-> a] }

====