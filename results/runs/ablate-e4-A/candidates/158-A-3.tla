---- MODULE Voting ----
EXTENDS Naturals, Integers, TLC

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES Votes, Thresholds

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Vote == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SafeValueAt(b, v) ==
  \A c \in Ballot :
    c < b =>
      \E q \in Quorum :
        \A a' \in q :
          (\E vote' \in Votes[a'] :
             vote'.ballot = c /\ vote'.value = v)
          \/ (Thresholds[a'] > c)

Chosen(v) ==
  \E b \in Ballot :
    \E q \in Quorum :
      \A a \in q :
        \E vote \in Votes[a] :
          vote.ballot = b /\ vote.value = v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Thresholds = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
PromiseIncrease ==
  /\ \E a \in Acceptor :
     \E nb \in Ballot :
       nb > Thresholds[a]
       /\ Votes' = Votes
       /\ Thresholds' = [Thresholds EXCEPT ![a] = nb]

VoteAction ==
  /\ \E a \in Acceptor :
     \E b \in Ballot :
       \E v \in Value :
         /\ b >= Thresholds[a]
         /\ ~(\E vote \in Votes[a] : vote.ballot = b)
         /\ ~(\E a' \in Acceptor \ {a} :
                \E vote' \in Votes[a'] :
                  vote'.ballot = b /\ vote'.value # v)
         /\ SafeValueAt(b, v)
         /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
         /\ Thresholds' = [Thresholds EXCEPT ![a] = b]

Next == PromiseIncrease \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Thresholds>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Votes \in [Acceptor -> SUBSET Vote]
  /\ Thresholds \in [Acceptor -> Int]

SafeVoteInvariant ==
  \A a \in Acceptor :
    \A v \in Votes[a] :
      \A c \in Ballot :
        c < v.ballot =>
          \E q \in Quorum :
            \A a' \in q :
              (\E vote' \in Votes[a'] :
                 vote'.ballot = c /\ vote'.value = v.value)
              \/ (Thresholds[a'] > c)

OneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      (\E a1 \in Acceptor :
         \E vote1 \in Votes[a1] :
           vote1.ballot = b /\ vote1.value = v1)
      /\ (\E a2 \in Acceptor :
            \E vote2 \in Votes[a2] :
              vote2.ballot = b /\ vote2.value = v2)
      => v1 = v2

AtMostOneChosen ==
  \A v1, v2 \in Value :
    Chosen(v1) /\ Chosen(v2) => v1 = v2

Inv == TypeOK /\ SafeVoteInvariant /\ OneValuePerBallot /\ AtMostOneChosen

\* ----------------------------------------------------------------------
\* Additional property (same as the safety invariant for model checking)
\* ----------------------------------------------------------------------
ConsensusSpecBar == AtMostOneChosen

=============================================================================