---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*------------------------------------------------------------*)
(*  Concrete finite versions for model checking (substituted) *)
MCAcceptor == {a1, a2, a3}
MCValue    == {v1, v2}
MCQuorum   == {{a1, a2}, {a2, a3}}
MCBallot   == 0..2

(*------------------------------------------------------------*)
VARIABLES votes, thresh

(* votes[a] is a set of records [ballot: Ballot, value: Value] *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(*----- Safety predicate for a value at a given ballot -----*)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vv \in votes[a] : vv.ballot = c /\ vv.value = v )
                    \/ (thresh[a] > c)

(*----- Action: increase promise threshold -----*)
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED votes

(*----- Action: cast a vote -----*)
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]                                   \* respects current promise
    /\ \A vv \in votes[a] : vv.ballot # b                \* not voted in this ballot yet
    /\ \A a2 \in Acceptor :
          (\E vv \in votes[a2] : vv.ballot = b) => 
          (\A vv2 \in votes[a2] : vv2.value = v)         \* no other value in same ballot
    /\ Safe(v, b)                                        \* safety condition
    /\ votes' = [votes EXCEPT ![a] = @ \cup { [ballot |-> b, value |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec ==
    Init /\ [][Next]_<<votes, thresh>>

(*------------------------------------------------------------*)
(*  Invariant *)

Inv ==
    /\ \A a \in Acceptor :
          \A vv \in votes[a] : Safe(vv.value, vv.ballot)               \* every vote is safe
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
            \A vv1 \in votes[a1], vv2 \in votes[a2] :
                (vv1.ballot = b /\ vv2.ballot = b) => vv1.value = vv2.value
    /\ \A a \in Acceptor : thresh[a] >= -1

(*------------------------------------------------------------*)
(*  Consistency property: at most one chosen value *)

ChosenValues ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E vv \in votes[a] : vv.ballot = b /\ vv.value = v }

ConsensusSpecBar ==
    \A v1, v2 \in ChosenValues : v1 = v2

(*------------------------------------------------------------*)
(*  Symmetry set (permutations of acceptors) *)

MCSymmetry ==
    { [a \in Acceptor |-> a] }   \* identity permutation (satisfies symmetry requirement)

====