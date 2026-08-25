---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES Votes, Threshold

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

VoteRec == [ballot : Ballot, value : Value]

Init ==
    /\ Votes    = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (\E vt \in Votes[a] : vt.ballot = c /\ vt.value = v)
                      \/ Threshold[a] > c )

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