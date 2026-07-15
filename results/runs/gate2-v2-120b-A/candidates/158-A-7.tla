---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*********************************************************************
  Constants (instantiated in the .cfg file)
  ----------------------------------------------------
  a1          : a distinguished acceptor (used only as a placeholder)
  Acceptor    : the finite set of acceptors
  Value       : the finite set of values that may be chosen
  Quorum      : a set of subsets of Acceptor, each representing a quorum
  Ballot      : the finite set of ballot numbers (natural numbers)
*********************************************************************)

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

(*********************************************************************
  Derived definitions
*********************************************************************)

(*-------------------------------------------------------------------*)
(* Overlap property of quorums: any two quorums intersect            *)
(* The .cfg file must ensure this property holds for the concrete   *)
(* instantiation.                                                     *)
(*-------------------------------------------------------------------*)
QuorumsOverlap == \A q1, q2 \in Quorum : q1 \cap q2 # {}

(*-------------------------------------------------------------------*)
(* Type of a vote: a record with fields 'bal' (ballot) and 'val'    *)
(*-------------------------------------------------------------------*)
Vote == [bal : Ballot, val : Value]

(*-------------------------------------------------------------------*)
(* Safety of a value at a ballot:                                      *)
(*   For every lower ballot c, there exists a quorum in which each    *)
(*   member either has already voted for the value in c, or can never*)
(*   vote in c (i.e., its promise threshold is > c).                  *)
(*-------------------------------------------------------------------*)
SafeAt(v, b, votes, thresh) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        \A a \in q :
          ( [bal |-> c, val |-> v] \in votes[a] ) \/ ( thresh[a] > c )

(*********************************************************************
  Variables
*********************************************************************)

VARIABLES votes,         \* votes[a] = set of votes cast by acceptor a
          thresh,        \* thresh[a] = promise threshold of acceptor a
          chosen         \* derived set of values that have become chosen

(*********************************************************************
  Init
*********************************************************************)

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]
  /\ chosen = {}

(*********************************************************************
  Actions
*********************************************************************)

(*-------------------------------------------------------------------*)
(* Increase the promise threshold of some acceptor to a higher ballot*)
(* without casting a vote.                                            *)
(*-------------------------------------------------------------------)
PromiseIncrease ==
  \E a \in Acceptor, newBal \in Ballot :
    /\ newBal > thresh[a]
    /\ /\ votes' = votes
       /\ thresh' = [thresh EXCEPT ![a] = newBal]
       /\ chosen' = chosen

(*-------------------------------------------------------------------*)
(* Cast a vote for value v in ballot b by acceptor a, subject to     *)
(* the four conditions described in the natural-language text.      *)
(*-------------------------------------------------------------------)
VoteCast ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= thresh[a]                               \* condition 1
    /\ ~(\E w \in votes[a] : w.bal = b)             \* condition 2
    /\ \A a2 \in Acceptor :
         ~(\E w \in votes[a2] : w.bal = b /\ w.val # v)   \* condition 3
    /\ SafeAt(v, b, votes, thresh)                  \* condition 4
    /\ /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [bal |-> b, val |-> v] }]
       /\ thresh' = [thresh EXCEPT ![a] = b]
       /\ chosen'  = chosen \cup {v}
       /\ UNCHANGED << >>

(*-------------------------------------------------------------------*)
(* All possible steps *)
(*-------------------------------------------------------------------)
Next ==
  \/ PromiseIncrease
  \/ VoteCast

(*********************************************************************
  Specification
*********************************************************************)

Spec == Init /\ [][Next]_<<votes, thresh, chosen>>

(*********************************************************************
  Invariant Inv: captures the three safety facts:
    1. every vote is safe at its ballot,
    2. at most one value per ballot,
    3. type correctness (ensured by the definitions).
*********************************************************************)

Inv ==
  /\ \A a \in Acceptor :
        /\ votes[a] \subseteq { v \in Vote : v.bal \in Ballot /\ v.val \in Value }
        /\ thresh[a] \in Ballot \cup {-1}
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( (\E a1 \in Acceptor : [bal |-> b, val |-> v1] \in votes[a1]) /\
            (\E a2 \in Acceptor : [bal |-> b, val |-> v2] \in votes[a2]) )
          => v1 = v2
  /\ \A a \in Acceptor :
        \A v \in votes[a] : SafeAt(v.val, v.bal, votes, thresh)

(*********************************************************************
  Property (the abstract consensus specification).  It states that the
  derived set 'chosen' contains at most one value.
*********************************************************************)

ConsensusSpecBar == Cardinality(chosen) <= 1

====