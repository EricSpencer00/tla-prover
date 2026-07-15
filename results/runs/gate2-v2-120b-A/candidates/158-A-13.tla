---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

VARIABLES votes, thresh

(* --constants that will be instantiated in the .cfg file-- *)
CONSTANTS Acceptor, Value, Quorum, Ballot

(* derived constant: the set of all possible votes *)
Vote == [ballot : Ballot, val : Value]

(* initial state *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* helper definitions *)
AcceptorSafeAt(a, b, v) ==
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]

(* there must be at least one quorum that makes the value safe at ballot b *)
ValueSafeAt(b, v) ==
    \E Q \in Quorum :
        \A a \in Q :
            (b \in { vt.ballot : vt \in votes[a] } => 
                \E vt \in votes[a] : vt.val = v /\ vt.ballot = b)
            \/ b < thresh[a]

(* actions *)

(* an acceptor raises its promise threshold *)
RaiseThresh(a) ==
    /\ a \in Acceptor
    /\ \E b \in Ballot :
        /\ b > thresh[a]
        /\ thresh' = [thresh EXCEPT ![a] = b]
        /\ UNCHANGED votes

(* an acceptor casts a vote for a value in a ballot *)
VoteAction(a) ==
    /\ a \in Acceptor
    /\ \E b \in Ballot, v \in Value :
        /\ b >= thresh[a]                     \* respects current promise
        /\ \A vt \in votes[a] : vt.ballot # b   \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
               (\E vt2 \in votes[a2] :
                    /\ vt2.ballot = b
                    /\ vt2.val # v) => FALSE   \* no other value voted in same ballot
        /\ ValueSafeAt(b, v)                  \* a quorum guarantees safety
        /\ votes' = [votes EXCEPT ![a] = 
                        votes[a] \cup { [ballot |-> b, val |-> v] }]
        /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor : RaiseThresh(a)
    \/ \E a \in Acceptor : VoteAction(a)

Spec ==
    Init /\ [][Next]_<<votes, thresh>>

(* invariants *)

(* type correctness of votes and thresholds *)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ thresh \in [Acceptor -> Int]

(* at most one value per ballot across all acceptors *)
OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( \E a1 \in Acceptor : [ballot |-> b, val |-> v1] \in votes[a1] )
            /\ ( \E a2 \in Acceptor : [ballot |-> b, val |-> v2] \in votes[a2] )
            => v1 = v2

(* every vote cast is safe at its ballot *)
VotesSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            ValueSafeAt(vt.ballot, vt.val)

Inv == /\ TypeOK /\ OneValuePerBallot /\ VotesSafe

(* safety property: at most one value can ever be chosen *)
ConsensusSpecBar ==
    \A b \in Ballot, v1, v2 \in Value :
        ( \E Q1 \in Quorum : \A a \in Q1 : [ballot |-> b, val |-> v1] \in votes[a] )
        /\ ( \E Q2 \in Quorum : \A a \in Q2 : [ballot |-> b, val |-> v2] \in votes[a] )
        => v1 = v2

====