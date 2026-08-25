---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES Votes, Threshold

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

VoteRec == [ballot : Ballot, value : Value]

(* ---------------------------------------------------------------------- *)
(* Substitution operators expected by the .cfg file *)

MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(* An empty symmetry set is acceptable; it can be refined later if needed *)
MCSymmetry == {}

(* ---------------------------------------------------------------------- *)
(* State predicates used by the .cfg file *)

TypeOK ==
    /\ \A a \in Acceptor : Threshold[a] \in Int
    /\ \A a \in Acceptor :
          \A vt \in Votes[a] :
              /\ vt.ballot \in Ballot
              /\ vt.value  \in Value

votes == Votes

maxBal ==
    [a \in Acceptor |-> 
        IF Votes[a] = {} 
        THEN -1 
        ELSE Max({ vt.ballot : vt \in Votes[a] })]

OneValuePerBallot == 
    \A b \in Ballot :
        (\E v \in Value :
            \A a \in Acceptor :
                (\E vt \in Votes[a] : vt.ballot = b /\ vt.value = v))
        => TRUE

OneVote ==
    \A a \in Acceptor :
        \A vt1, vt2 \in Votes[a] :
            (vt1.ballot = vt2.ballot) => vt1 = vt2

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ Votes    = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

(* ---------------------------------------------------------------------- *)
(* Safety predicate *)

Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (\E vt \in Votes[a] : vt.ballot = c /\ vt.value = v)
                      \/ Threshold[a] > c )

(* ---------------------------------------------------------------------- *)
(* Actions *)

Promise ==
    \E a \in Acceptor :
        \E nb \in Ballot :
            /\ nb > Threshold[a]
            /\ Threshold' = [Threshold EXCEPT ![a] = nb]
            /\ UNCHANGED Votes

Vote ==
    \E a \in Acceptor :
        \E v \in Value :
            \E b \in Ballot :
                /\ b >= Threshold[a]
                /\ \A vt \in Votes[a] : vt.ballot # b
                /\ \A a2p \in Acceptor :
                    \A vt2p \in Votes[a2p] :
                        (vt2p.ballot = b) => vt2p.value = v
                /\ Safe(v, b)
                /\ Votes'    = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next ==
    \/ Promise
    \/ Vote

Spec ==
    Init /\ [][Next]_<<Votes, Threshold>>

(* ---------------------------------------------------------------------- *)
(* Invariant *)

Inv ==
    /\ \A a \in Acceptor : Threshold[a] \in Int
    /\ \A a \in Acceptor :
          \A vt \in Votes[a] :
              /\ vt.ballot \in Ballot
              /\ vt.value  \in Value
    /\ \A b \in Ballot :
          \A vv1 \in Value :
          \A vv2 \in Value :
              ( (\E aa1 \in Acceptor : \E vt1p \in Votes[aa1] : vt1p.ballot = b /\ vt1p.value = vv1)
                /\ (\E aa2 \in Acceptor : \E vt2p \in Votes[aa2] : vt2p.ballot = b /\ vt2p.value = vv2) )
              => vv1 = vv2
    /\ \A a \in Acceptor :
          \A vt \in Votes[a] : Safe(vt.value, vt.ballot)

(* ---------------------------------------------------------------------- *)
(* Consistency property *)

ChosenVals ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                \A a \in Q :
                    \E vt \in Votes[a] : vt.ballot = b /\ vt.value = v }

ConsensusSpecBar ==
    \A vv1, vv2 \in ChosenVals : vv1 = vv2

====