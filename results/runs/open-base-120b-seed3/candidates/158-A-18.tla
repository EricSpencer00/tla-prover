---- MODULE Voting ----
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Operators substituted for the constants (usually identity)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, promised

\* ----------------------------------------------------------------------
\*  Safety predicate: a value v is safe at ballot b
\* ----------------------------------------------------------------------
Safe(b, v) ==
  \A c \in Ballot :
    (c < b) => 
      (\E Q \in Quorum :
        \A a \in Q :
          ( <<c, v>> \in votes[a] ) \/ ( promised[a] > c )
      )

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes    = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\*  Action: raise an acceptor's promise threshold
\* ----------------------------------------------------------------------
PromiseIncrease ==
  \E a \in Acceptor:
    \E b \in Ballot:
      /\ b > promised[a]
      /\ promised' = [promised EXCEPT ![a] = b]
      /\ UNCHANGED votes

\* ----------------------------------------------------------------------
\*  Action: an acceptor votes for a value in a ballot
\* ----------------------------------------------------------------------
VoteAction ==
  \E a \in Acceptor:
    \E b \in Ballot:
      \E v \in Value:
        /\ b >= promised[a]                                 \* respects promise
        /\ <<b, v>> \notin votes[a]                         \* not voted in b yet
        /\ \A a2 \in Acceptor:
              \A v2 \in Value:
                (<<b, v2>> \in votes[a2]) => v2 = v        \* at most one value per ballot
        /\ Safe(b, v)                                       \* value is safe
        /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup { <<b, v>> }]
        /\ promised' = [promised EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ PromiseIncrease
  \/ VoteAction

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<votes, promised>>

\* ----------------------------------------------------------------------
\*  Invariant: type correctness, safety of every vote, and uniqueness per ballot
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in Acceptor:
        /\ votes[a] \subseteq Ballot \X Value
        /\ promised[a] \in Ballot \cup {-1}
        /\ \A <<b, v>> \in votes[a] : Safe(b, v)
  /\ \A b \in Ballot:
        \A a1, a2 \in Acceptor:
          \A v1, v2 \in Value:
            (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

\* ----------------------------------------------------------------------
\*  Consistency property: at most one value can ever be chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    ( (\E b \in Ballot: \E Q \in Quorum: \A a \in Q: <<b, v1>> \in votes[a]) /\
      (\E b' \in Ballot: \E Q' \in Quorum: \A a \in Q': <<b', v2>> \in votes[a]) )
      => v1 = v2

\* ----------------------------------------------------------------------
\*  Symmetry set (identity permutation suffices)
\* ----------------------------------------------------------------------
MCSymmetry ==
  { [a \in Acceptor |-> a] }

====