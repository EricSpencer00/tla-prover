---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* --------------------------------------------------------------------- *)
(*  Constants used by the model checker (aliases)                        *)
(* --------------------------------------------------------------------- *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(* --------------------------------------------------------------------- *)
(*  Basic assumptions about the constants                                 *)
(* --------------------------------------------------------------------- *)
ASSUME Acceptor = {a1, a2, a3}
ASSUME Value    = {v1, v2}
ASSUME /\ Quorum \subseteq SUBSET Acceptor
       /\ \A q1, q2 \in Quorum : q1 # {} /\ q2 # {} => q1 \cap q2 # {}

(* --------------------------------------------------------------------- *)
(*  Variables                                                            *)
(* --------------------------------------------------------------------- *)
VARIABLES votes, threshold

(* --------------------------------------------------------------------- *)
(*  Types                                                                *)
(* --------------------------------------------------------------------- *)
Vote == [ballot : Ballot, value : Value]

(* --------------------------------------------------------------------- *)
(*  Initial state                                                        *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(* --------------------------------------------------------------------- *)
(*  Safety predicate for a value at a ballot                             *)
(* --------------------------------------------------------------------- *)
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( ([ballot |-> c, value |-> v] \in votes[a])
                      \/ (threshold[a] > c) )

(* --------------------------------------------------------------------- *)
(*  Actions                                                              *)
(* --------------------------------------------------------------------- *)
Promise(a, newb) ==
    /\ a \in Acceptor
    /\ newb \in Ballot
    /\ newb > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = newb]
    /\ UNCHANGED votes

VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]
    /\ ~([ballot |-> b, value |-> v] \in votes[a])
    /\ \A a2 \in Acceptor :
          \A vv \in Value :
              (([ballot |-> b, value |-> vv] \in votes[a2]) => vv = v)
    /\ Safe(b, v)
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, nb \in Ballot : Promise(a, nb)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteAction(a, b, v)

(* --------------------------------------------------------------------- *)
(*  Specification                                                        *)
(* --------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<votes, threshold>>

(* --------------------------------------------------------------------- *)
(*  Invariant                                                            *)
(* --------------------------------------------------------------------- *)
Inv ==
    /\ \A a \in Acceptor : threshold[a] \in Ballot \/ threshold[a] = -1
    /\ \A a \in Acceptor : votes[a] \subseteq Vote
    /\ \A a \in Acceptor :
          \A vt \in votes[a] : Safe(vt.ballot, vt.value)
    /\ \A b \in Ballot :
          \A v1, v2 \in Value :
              ( (\E a1 \in Acceptor : [ballot |-> b, value |-> v1] \in votes[a1])
                /\ (\E a2 \in Acceptor : [ballot |-> b, value |-> v2] \in votes[a2]) )
                => v1 = v2

(* --------------------------------------------------------------------- *)
(*  Definition of a chosen value                                         *)
(* --------------------------------------------------------------------- *)
Chosen(v) ==
    \E b \in Ballot :
        \E q \in Quorum :
            \A a \in q : [ballot |-> b, value |-> v] \in votes[a]

(* --------------------------------------------------------------------- *)
(*  Safety property (consensus)                                          *)
(* --------------------------------------------------------------------- *)
ConsensusSpecBar == 
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(* --------------------------------------------------------------------- *)
(*  Symmetry set (identity permutation)                                 *)
(* --------------------------------------------------------------------- *)
MCSymmetry == { [a \in Acceptor |-> a] }

====