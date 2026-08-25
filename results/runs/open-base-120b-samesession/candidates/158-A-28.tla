---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Operators substituted by the model checker (constants may be
  replaced by bounded versions)
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue   == Value
MCQuorum  == Quorum
MCBallot  == Ballot

VARIABLES votes, thresh

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

(* a vote is a pair <<ballot, value>> *)
VotePair == [b : Ballot, v : Value]

(* Safe(v,b) : value v is safe to be chosen at ballot b *)
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          (<<c, v>> \in votes[a]) \/ (thresh[a] > c)

(* No two different values are voted for the same ballot *)
NoConflictingVotes ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      \A v1, v2 \in Value :
        (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

(* The set of values that have been "chosen": a quorum has all
   members voting for the same value in the same ballot *)
Chosen ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q : <<b, v>> \in votes[a] }

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* Increase the promise threshold of an acceptor *)
PromiseIncrease ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > thresh[a]
      /\ UNCHANGED votes
      /\ thresh' = [thresh EXCEPT ![a] = b]

(* Cast a vote for value v in ballot b *)
Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= thresh[a]                     \* not below current promise
        /\ ~(\E vv \in votes[a] : vv[0] = b)   \* hasn't voted in this ballot
        /\ (\A a2 \in Acceptor :
              \A vv \in votes[a2] :
                (vv[0] = b) => vv[1] = v)      \* no other value for same ballot
        /\ Safe(v, b)                         \* safety condition
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
        /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ PromiseIncrease
  \/ Vote

Spec ==
  Init /\ [][Next]_<<votes, thresh>>

(*--------------------------------------------------------------------
  Invariant
--------------------------------------------------------------------*)
Inv ==
  /\ \A a \in Acceptor : thresh[a] \in (Ballot \cup {-1})
  /\ \A a \in Acceptor : votes[a] \subseteq (Ballot \X Value)
  /\ \A a \in Acceptor :
        \A vv \in votes[a] : Safe(vv[1], vv[0])
  /\ NoConflictingVotes

(*--------------------------------------------------------------------
  Safety property: at most one value can be chosen
--------------------------------------------------------------------*)
ConsensusSpecBar ==
  [] ( \A v1, v2 \in Value :
          (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2 )

(*--------------------------------------------------------------------
  Symmetry set (identity permutation only, sufficient for small models)
--------------------------------------------------------------------*)
MCSymmetry ==
  { [a \in Acceptor |-> a] }

=============================================================================