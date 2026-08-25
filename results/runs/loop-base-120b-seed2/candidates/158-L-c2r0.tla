---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* operators overridden by the .cfg *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES Votes, Threshold

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

VoteRec == [ballot : Ballot, value : Value]

Init ==
    /\ Votes    = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

Safe(v, b) ==
    \A c \in Ballot :
        c < b =>
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
                /\ \A a2 \in Acceptor :
                    \A vt2 \in Votes[a2] :
                        (vt2.ballot = b) => vt2.value = v
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
          \A v1 \in Value :
          \A v2 \in Value :
              ( (\E a1 \in Acceptor : \E vt1 \in Votes[a1] : vt1.ballot = b /\ vt1.value = v1)
                /\ (\E a2 \in Acceptor : \E vt2 \in Votes[a2] : vt2.ballot = b /\ vt2.value = v2) )
              => v1 = v2
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
    \A v1, v2 \in ChosenVals : v1 = v2

(* ---------------------------------------------------------------------- *)
(* Symmetry set *)

MCSymmetry ==
    { [a \in Acceptor |-> a] }

====