---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* Substitutable constants for model checking *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES Votes, Promise

(* a vote is a record containing a ballot number and a value *)
VoteRecord == [ballot : Ballot, value : Value]

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ Votes   = [a \in Acceptor |-> {}]
  /\ Promise = [a \in Acceptor |-> -1]

(* --------------------------------------------------------------------- *)
(* Safety predicate: a value v is safe at ballot b *)
Safe(v, b) ==
  \A c \in Ballot :
    c < b =>
      \E Q \in Quorum :
        \A a \in Q :
          (\E vote \in Votes[a] :
               vote.ballot = c /\ vote.value = v) \/ Promise[a] >= c

(* --------------------------------------------------------------------- *)
(* Actions *)

Increase ==
  \E a \in Acceptor: \E b \in Ballot :
    /\ b > Promise[a]
    /\ UNCHANGED Votes
    /\ Promise' = [Promise EXCEPT ![a] = b]

CastVote ==
  \E a \in Acceptor: \E b \in Ballot: \E v \in Value :
    /\ b >= Promise[a]                         \* cannot vote below promise
    /\ \A vote \in Votes[a] : vote.ballot # b  \* no prior vote in this ballot
    /\ \A a2 \in Acceptor: \A vote2 \in Votes[a2] :
         (vote2.ballot = b) => vote2.value = v \* at most one value per ballot
    /\ Safe(v, b)                               \* value is safe
    /\ Votes'   = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ Promise' = [Promise EXCEPT ![a] = b]

Next == Increase \/ CastVote

vars == <<Votes, Promise>>

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Invariant *)

TypeInvariant ==
  /\ \A a \in Acceptor : Votes[a] \subseteq [ballot : Ballot, value : Value]

AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A a1 \in Acceptor : \A a2 \in Acceptor :
      ( \E vote1 \in Votes[a1] : vote1.ballot = b ) /\
      ( \E vote2 \in Votes[a2] : vote2.ballot = b ) =>
        (\A vote1 \in Votes[a1] : \A vote2 \in Votes[a2] :
            (vote1.ballot = b /\ vote2.ballot = b) => vote1.value = vote2.value)

AllVotesSafe ==
  \A a \in Acceptor : \A vote \in Votes[a] : Safe(vote.value, vote.ballot)

Inv == TypeInvariant /\ AtMostOneValuePerBallot /\ AllVotesSafe

(* --------------------------------------------------------------------- *)
(* Consistency property *)

ChosenVals ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
          \E vote \in Votes[a] : vote.ballot = b /\ vote.value = v }

ConsensusSpecBar == Cardinality(ChosenVals) <= 1

(* --------------------------------------------------------------------- *)
(* Symmetry set (permutations of acceptors) *)

MCSymmetry ==
  {
    [a \in Acceptor |-> a],
    [a \in Acceptor |-> IF a = a1 THEN a2 ELSE IF a = a2 THEN a1 ELSE a]
  }

====