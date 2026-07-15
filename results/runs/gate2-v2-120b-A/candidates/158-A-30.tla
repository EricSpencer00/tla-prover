---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT Acceptor   \* Set of acceptor identifiers
CONSTANT Value      \* Set of values that can be chosen
CONSTANT Quorum     \* Set of quorums, each quorum is a subset of Acceptor
CONSTANT Ballot     \* Set of ballot numbers (natural numbers)

(*-----------------------------------------------------------------
  Derived constants used for readability
-----------------------------------------------------------------*)
Quorums == Quorum

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLE 
    votes,       \* [a \in Acceptor -> SUBSET Ballot \X Value]
    threshold    \* [a \in Acceptor -> Nat]   (promise threshold)

(*-----------------------------------------------------------------
  Type correctness invariant (auxiliary, not exported)
-----------------------------------------------------------------*)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> Nat]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> 0]   \* 0 acts as “negative one” in natural numbers

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Ballots == Ballot

HasVote(a, b, v) == <<a, b, v>> \in
    UNION { <<a, b, v>> : a \in Acceptor, b \in Ballot, v \in Value : 
            <<b, v>> \in votes[a] }

QuorumIntersection ==
    \A q1, q2 \in Quorums : q1 \cap q2 # {}

(* A value is safe at ballot b if for every lower ballot c there exists a quorum
   whose members have either voted for that value in c or have threshold > c. *)
SafeAt(v, b) ==
    \A c \in Ballots :
        (c < b) => 
            \E q \in Quorums :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

(* 1. Increase promise threshold without voting *)
Promote ==
    \E a \in Acceptor :
        \E newThr \in Ballots :
            /\ newThr > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = newThr]
            /\ votes' = votes

(* 2. Cast a vote for a value in a ballot, respecting safety and quorum *)
Vote ==
    \E a \in Acceptor :
        \E b \in Ballots :
            \E v \in Value :
                /\ b >= threshold[a]                     \* not below current promise
                /\ ~(\E vv \in Value : <<b, vv>> \in votes[a])   \* haven't voted in b yet
                /\ \A a2 \in Acceptor :
                       (<<b, v2>> \in votes[a2]) => v2 = v   \* no other value in same ballot
                /\ \E q \in Quorums :
                        \A a2 \in q :
                            (threshold[a2] > b) \/ (<<b, v>> \in votes[a2]) 
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                /\ threshold' = [threshold EXCEPT ![a] = b]

(* 3. Stuttering step to satisfy weak fairness without changing state *)
Stutter ==
    UNCHANGED <<votes, threshold>>

Next ==
    \/ Promote
    \/ Vote
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-----------------------------------------------------------------
  Invariant required by the cfg: Inv
-----------------------------------------------------------------*)
Inv ==
    /\ TypeOK
    /\ QuorumIntersection
    /\ \A a \in Acceptor :
          \A <<b, v>> \in votes[a] : SafeAt(v, b)

(*-----------------------------------------------------------------
  Property required by the cfg: ConsensusSpecBar
  (Consistency: at most one value is ever chosen)
-----------------------------------------------------------------*)
ChosenValues ==
    { v \in Value :
        \E b \in Ballots :
            \E q \in Quorums :
                \A a \in q : <<b, v>> \in votes[a] }

ConsensusSpecBar ==
    Cardinality(ChosenValues) <= 1

=============================================================================