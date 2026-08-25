---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*-----------------------------------------------------------------
  Operators used for model checking substitution
-----------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES votes, threshold

(*-----------------------------------------------------------------
  Type correctness
-----------------------------------------------------------------*)
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
  /\ threshold \in [Acceptor -> Int]

(*-----------------------------------------------------------------
  Safety of a value at a given ballot
-----------------------------------------------------------------*)
Safe(val, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E v \in votes[a] :
                /\ v.ballot = c
                /\ v.value  = val )
          \/ threshold[a] > c

(*-----------------------------------------------------------------
  Invariant that every cast vote is safe at its ballot
-----------------------------------------------------------------*)
AllVotesSafe ==
  \A a \in Acceptor :
    \A v \in votes[a] :
      Safe(v.value, v.ballot)

(*-----------------------------------------------------------------
  Invariant that at most one value is voted for per ballot
-----------------------------------------------------------------*)
OneValuePerBallot ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      \A v1 \in votes[a1] :
        \A v2 \in votes[a2] :
          ( /\ v1.ballot = b
            /\ v2.ballot = b )
          => v1.value = v2.value

(*-----------------------------------------------------------------
  Overall invariant
-----------------------------------------------------------------*)
Inv == TypeOK /\ AllVotesSafe /\ OneValuePerBallot

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------
  Action: an acceptor raises its promise threshold
-----------------------------------------------------------------*)
Promise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > threshold[a]
      /\ threshold' = [threshold EXCEPT ![a] = b]
      /\ UNCHANGED votes

(*-----------------------------------------------------------------
  Action: an acceptor casts a vote for a value in a ballot
-----------------------------------------------------------------*)
Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E val \in Value :
        /\ b >= threshold[a]                                          \* ballot not below promise
        /\ \A v \in votes[a] : v.ballot # b                           \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
              \A v2 \in votes[a2] :
                (v2.ballot = b) => v2.value = val                    \* no conflicting vote
        /\ Safe(val, b)                                               \* value is safe at b
        /\ votes' = [votes EXCEPT ![a] = @ \cup { [ballot |-> b, value |-> val] }]
        /\ threshold' = [threshold EXCEPT ![a] = b]
        /\ UNCHANGED << >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next == Promise \/ Vote

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*-----------------------------------------------------------------
  Definition of chosen values
-----------------------------------------------------------------*)
ChosenVals ==
  { val \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E v \in votes[a] :
                /\ v.ballot = b
                /\ v.value  = val }

(*-----------------------------------------------------------------
  Property: at most one value can be chosen
-----------------------------------------------------------------*)
ConsensusSpecBar == \A v1, v2 \in ChosenVals : v1 = v2

(*-----------------------------------------------------------------
  Symmetry set (identity permutation is sufficient)
-----------------------------------------------------------------*)
MCSymmetry == { [a \in Acceptor |-> a] }

====