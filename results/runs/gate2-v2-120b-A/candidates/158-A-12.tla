---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
AcceptorSet == Acceptor
ValueSet    == Value
QuorumSet   == Quorum
BallotSet   == Ballot

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Vote == [ballot : BallotSet, val : ValueSet]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES votes, thresh, chosen

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* votes[a] is the set of votes cast by acceptor a *)
Votes == [a \in AcceptorSet |-> { v \in Vote : v \in votes[a] }]

(* thresh[a] is the promise threshold of acceptor a *)
Thresh == [a \in AcceptorSet |-> thresh[a]]

(* quorum intersection property (assumed to hold for the constant set Quorum) *)
QuorumIntersection ==
  \A q1, q2 \in QuorumSet : q1 \cap q2 # {}

(* A value v is safe at ballot b under the current state *)
Safe(v, b) ==
  \A c \in 0..b-1 :
    \E q \in QuorumSet :
      \A a \in q :
        (\E w \in votes[a] : w.ballot = c /\ w.val = v) \/ thresh[a] > c

(* A quorum q has all members voting for value v in ballot b *)
QuorumVoted(q, b, v) ==
  \A a \in q : \E w \in votes[a] : w.ballot = b /\ w.val = v

(* A value is chosen if some quorum has all members voting for it in some ballot *)
Chosen(v) ==
  \E b \in BallotSet :
    \E q \in QuorumSet : QuorumVoted(q, b, v)

(* The set of all chosen values (derived from votes) *)
ChosenSet == { v \in ValueSet : Chosen(v) }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ votes = [a \in AcceptorSet |-> {}]
  /\ thresh = [a \in AcceptorSet |-> -1]
  /\ chosen = {}

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* An acceptor raises its promise threshold without voting *)
Promise ==
  \E a \in AcceptorSet :
    \E n \in BallotSet :
      /\ n > thresh[a]
      /\ \A w \in votes[a] : w.ballot < n
      /\ UNCHANGED << votes, chosen >>
      /\ thresh' = [thresh EXCEPT ![a] = n]

(* An acceptor votes for a value in a ballot, respecting all constraints *)
VoteAct ==
  \E a \in AcceptorSet :
    \E b \in BallotSet :
      \E v \in ValueSet :
        /\ b >= thresh[a]
        /\ \A w \in votes[a] : w.ballot # b
        /\ \A a2 \in AcceptorSet :
            \A w2 \in votes[a2] :
              (w2.ballot = b) => (w2.val = v)
        /\ Safe(v, b)
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {{ballot |-> b, val |-> v}}]
        /\ thresh' = [thresh EXCEPT ![a] = b]
        /\ chosen' = IF Chosen(v) THEN chosen
                     ELSE chosen \cup {v}
        /\ UNCHANGED << >>

(* The next-state relation *)
Next ==
  \/ Promise
  \/ VoteAct

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, thresh, chosen>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

(* Type correctness invariant *)
TypeOK ==
  /\ votes \in [AcceptorSet -> SUBSET Vote]
  /\ thresh \in [AcceptorSet -> Nat \cup {-1}]
  /\ chosen \in SUBSET ValueSet

(* Safety invariant: the set of chosen values contains at most one value *)
AtMostOneChosen ==
  Cardinality(chosen) <= 1

(* Combined invariant required by the .cfg *)
Inv == TypeOK /\ AtMostOneChosen

(*--------------------------------------------------------------------
  Safety property (same as the invariant but exposed as a property)
--------------------------------------------------------------------*)
ConsensusSpecBar == AtMostOneChosen

=============================================================================