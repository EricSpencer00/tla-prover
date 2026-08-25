---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*-------------------------------------------------------------------*)
(*  Substituted constants for model checking                           *)
(*-------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(*-------------------------------------------------------------------*)
(*  State variables                                                  *)
(*-------------------------------------------------------------------*)
VARIABLES votes, threshold

(*-------------------------------------------------------------------*)
(*  Types                                                             *)
(*-------------------------------------------------------------------*)
VoteRecord == [ballot : Ballot, value : Value]

(*-------------------------------------------------------------------*)
(*  Safety predicate: a value is safe at a ballot                    *)
(*-------------------------------------------------------------------*)
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vr \in votes[a] : vr.ballot = c /\ vr.value = v )
          \/ (threshold[a] > c)

(*-------------------------------------------------------------------*)
(*  Initialization                                                   *)
(*-------------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

(*-------------------------------------------------------------------*)
(*  Promise action: increase threshold                               *)
(*-------------------------------------------------------------------*)
Promise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

(*-------------------------------------------------------------------*)
(*  Vote action                                                      *)
(*-------------------------------------------------------------------*)
Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= threshold[a]                                 \* not below current promise
  /\ ~(\E vr \in votes[a] : vr.ballot = b)              \* hasn't voted in this ballot
  /\ \A a2 \in Acceptor :
        \A vr \in votes[a2] :
          (vr.ballot = b) => (vr.value = v)            \* no conflicting vote
  /\ Safe(v, b)                                         \* value is safe
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
  /\ threshold' = [threshold EXCEPT ![a] = b]

(*-------------------------------------------------------------------*)
(*  Next-state relation                                               *)
(*-------------------------------------------------------------------*)
Next ==
  \E a \in Acceptor :
    \/ \E b \in Ballot : Promise(a, b)
    \/ \E b \in Ballot, v \in Value : Vote(a, b, v)

(*-------------------------------------------------------------------*)
(*  Specification                                                    *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-------------------------------------------------------------------*)
(*  Invariant: every vote is safe and at most one value per ballot   *)
(*-------------------------------------------------------------------*)
Inv ==
  /\ \A a \in Acceptor :
        \A vr \in votes[a] : Safe(vr.value, vr.ballot)
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( (\E a1 \in Acceptor : \E vr1 \in votes[a1] : vr1.ballot = b /\ vr1.value = v1) 
            /\ (\E a2 \in Acceptor : \E vr2 \in votes[a2] : vr2.ballot = b /\ vr2.value = v2) )
          => v1 = v2

(*-------------------------------------------------------------------*)
(*  Consistency property: at most one chosen value                  *)
(*-------------------------------------------------------------------*)
Chosen ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E vr \in votes[a] : vr.ballot = b /\ vr.value = v }

ConsensusSpecBar == Cardinality(Chosen) <= 1

(*-------------------------------------------------------------------*)
(*  Symmetry set (trivial identity permutation)                     *)
(*-------------------------------------------------------------------*)
MCSymmetry == { [a \in Acceptor |-> a] }

====