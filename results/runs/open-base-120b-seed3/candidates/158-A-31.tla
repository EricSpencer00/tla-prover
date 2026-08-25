---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* substitution operators that the .cfg may override *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

VoteRec == [ballot : Ballot, value : Value]

(* initial state *)
Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(* safety of a value at a ballot *)
Safe(b, val) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    ( [ballot |-> c, value |-> val] \in votes[a] )
                    \/ (threshold[a] > c)

(* an acceptor raises its promise threshold *)
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

(* an acceptor casts a vote *)
Vote(a, b, val) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ val \in Value
    /\ b >= threshold[a]                         \* respects current promise
    /\ \A v \in votes[a] : v.ballot # b          \* has not voted in this ballot yet
    /\ \A a2 \in Acceptor :
          \A v \in votes[a2] :
              (v.ballot = b) => v.value = val   \* at most one value per ballot
    /\ Safe(b, val)                              \* value is safe
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> val] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_<<votes, threshold>>

(* invariant capturing type correctness, safety of every vote, and single value per ballot *)
Inv ==
    /\ \A a \in Acceptor : threshold[a] >= -1
    /\ \A a \in Acceptor :
          \A v \in votes[a] :
              ( v.ballot \in Ballot
                /\ v.value \in Value
                /\ Safe(v.ballot, v.value) )
    /\ \A b \in Ballot, v1, v2 \in Value :
          ( (\E a \in Acceptor : [ballot |-> b, value |-> v1] \in votes[a])
            /\ (\E a \in Acceptor : [ballot |-> b, value |-> v2] \in votes[a]) )
          => v1 = v2

(* definition of a chosen value: a quorum all voted for the same value in the same ballot *)
Chosen(b, val, Q) ==
    Q \in Quorum /\ \A a \in Q : [ballot |-> b, value |-> val] \in votes[a]

(* the consensus safety property *)
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        ( \E b1 \in Ballot, Q1 \in Quorum : Chosen(b1, v1, Q1) )
        /\ ( \E b2 \in Ballot, Q2 \in Quorum : Chosen(b2, v2, Q2) )
        => v1 = v2

(* symmetry set – identity permutation (can be extended) *)
MCSymmetry == { [a \in Acceptor |-> a] }

====