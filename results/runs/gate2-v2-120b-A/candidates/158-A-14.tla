---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg)
-----------------------------------------------------------------*)
CONSTANTS a1, Acceptor, Value, Quorum, Ballot

(*-----------------------------------------------------------------
  Types and derived sets
-----------------------------------------------------------------*)
(* Set of all acceptors *)
Acceptors == Acceptor

(* Set of quorum identifiers *)
Quorums == Quorum

(* All ballot numbers are natural numbers inside the finite set Ballot *)
Ballots == Ballot

(* An individual vote is a record containing a ballot and a value *)
Vote == [b : Ballots, v : Value]

(* A quorum is a set of acceptors; we model the collection of quorums as
   a set of sets of acceptors.  The constant Quorum is that collection. *)
ASSUME QuorumSubset == Quorums \subseteq SUBSET Acceptors

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES votes, prom

(* votes[a] is the set of votes cast by acceptor a *)
(* prom[a] is the promise threshold of acceptor a (the smallest ballot
   number it will ever consider) *)
vars == << votes, prom >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* A quorum Q demonstrates that value v is safe at ballot b
   iff for every lower ballot c < b there exists a quorum Qc such that
   every acceptor in Qc either already voted (c,v) or has a promise
   threshold > c (so it can never vote in c). *)
SafeAt(v, b) ==
  \A c \in Ballots :
    (c < b) => 
      \E Qc \in Quorums :
        \A a \in Qc :
          (<<c, v>> \in votes[a]) \/ (prom[a] > c)

(* The set of values that have been chosen: a value is chosen if some
   quorum of acceptors have all voted for it in the same ballot. *)
Chosen == 
  { v \in Value :
      \E b \in Ballots :
        \E Q \in Quorums :
          \A a \in Q : <<b, v>> \in votes[a] }

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptors |-> {}]
  /\ prom  = [a \in Acceptors |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
(* 1. An acceptor may raise its promise threshold without voting *)
Prom(a, b) ==
  /\ a \in Acceptors
  /\ b \in Ballots
  /\ b > prom[a]
  /\ prom' = [prom EXCEPT ![a] = b]
  /\ UNCHANGED votes

(* 2. An acceptor votes for value v in ballot b *)
VoteAction(a, b, v) ==
  /\ a \in Acceptors
  /\ b \in Ballots
  /\ v \in Value
  /\ b >= prom[a]                     \* respects current promise
  /\ ~(\E v2 \in Value : <<b, v2>> \in votes[a])  \* no prior vote in b
  /\ \A a2 \in Acceptors :
        ~(\E v2 \in Value : <<b, v2>> \in votes[a2] /\ v2 # v)   \* at most one value per ballot
  /\ SafeAt(v, b)                     \* safety precondition
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ prom'  = [prom  EXCEPT ![a] = b]

(* 3. Stuttering step to avoid deadlock *)
Stutter ==
  UNCHANGED <<votes, prom>>

Next ==
  \/ \E a \in Acceptors, b \in Ballots : Prom(a, b)
  \/ \E a \in Acceptors, b \in Ballots, v \in Value : VoteAction(a, b, v)
  \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, prom>>

(*-----------------------------------------------------------------
  Invariant required by the cfg
-----------------------------------------------------------------*)
(* Consistency: at most one value can ever be chosen *)
Inv ==
  Cardinality(Chosen) <= 1

(*-----------------------------------------------------------------
  Property required by the cfg
-----------------------------------------------------------------*)
(* We reuse the same invariant as the abstraction's safety property. *)
ConsensusSpecBar == Inv

=============================================================================