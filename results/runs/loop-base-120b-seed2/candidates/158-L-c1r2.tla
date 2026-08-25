---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Operators substituting for the constants in the model checking cfg
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, thresh

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* a vote is a pair <<ballot, value>>
BallotValue == Ballot \X Value

IsPermutation(f) ==
  /\ \A x, y \in Acceptor : f[x] = f[y] => x = y
  /\ \A b \in Acceptor : \E a \in Acceptor : f[a] = b

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsPermutation(f) }

Safe(v, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ((<<c, v>> \in votes[a]) \/ (thresh[a] > c))

OneValuePerBallot ==
  \A b \in Ballot :
    \A a1_, a2_ \in Acceptor :
      \A v1_, v2_ \in Value :
        (<<b, v1_>> \in votes[a1_] /\ <<b, v2_>> \in votes[a2_]) => v1_ = v2_

AllVotesSafe ==
  \A a \in Acceptor :
    \A p \in votes[a] :
      Safe(p[2], p[1])

TypeCorrectness ==
  /\ votes \in [Acceptor -> SUBSET BallotValue]
  /\ thresh \in [Acceptor -> Int]

OverlapQuorums ==
  \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Inv == 
  /\ AllVotesSafe
  /\ OneValuePerBallot
  /\ TypeCorrectness
  /\ OverlapQuorums

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Promise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= thresh[a]
  /\ \A p \in votes[a] : p[1] # b          \* not already voted in ballot b
  /\ \A a2_ \in Acceptor :
        a2_ # a => 
          \A p \in votes[a2_] :
            (p[1] = b) => p[2] = v          \* no other value in same ballot
  /\ Safe(v, b)                            \* safety condition
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_<<votes, thresh>>

(*--------------------------------------------------------------------
  Consensus property
--------------------------------------------------------------------*)
ChosenVals ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q : <<b, v>> \in votes[a] }

ConsensusSpecBar == Cardinality(ChosenVals) <= 1

====