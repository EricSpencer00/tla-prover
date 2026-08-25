---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* --------------  Operators for model checking substitution --------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* --------------  Variables --------------
VARIABLES votes, threshold

\* --------------  Types --------------
TypeInvariant ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Int]

\* --------------  Safety of a vote --------------
Safe(b, v) ==
  \A c \in Ballot :
    (c < b) => 
      \E q \in Quorum :
        /\ q # {}
        /\ \A a \in q :
            (<<c, v>> \in votes[a]) \/ (c < threshold[a])

\* --------------  Invariant: every cast vote is safe --------------
AllVotesSafe ==
  \A a \in Acceptor :
    \A p \in votes[a] :
      Safe(p[1], p[2])

\* --------------  Invariant: at most one value per ballot --------------
OneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\ 
        (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

\* --------------  Overall invariant --------------
Inv == TypeInvariant /\ AllVotesSafe /\ OneValuePerBallot

\* --------------  Initial state --------------
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* --------------  Actions --------------

\* Promise to a higher ballot (no vote)
PromiseIncrease ==
  \E a \in Acceptor :
    \E nb \in Ballot :
      /\ nb > threshold[a]
      /\ threshold' = [threshold EXCEPT ![a] = nb]
      /\ UNCHANGED votes

\* Vote for a value in a ballot
Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= threshold[a]
        /\ <<b, v>> \notin votes[a]
        /\ (\A a2 \in Acceptor :
              \A v2 \in Value :
                (<<b, v2>> \in votes[a2]) => v2 = v)
        /\ Safe(b, v)
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
        /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \/ PromiseIncrease \/ Vote

\* --------------  Specification --------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* --------------  Consistency property (Consensus) --------------
ConsensusSpecBar ==
  \A q1, q2 \in Quorum :
    \A b1, b2 \in Ballot :
      \A v1, v2 \in Value :
        ( (\A a \in q1 : <<b1, v1>> \in votes[a]) /\ 
          (\A a \in q2 : <<b2, v2>> \in votes[a]) ) => v1 = v2

\* --------------  Symmetry (permutations of acceptors) --------------
IsPermutation(f) ==
  /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
  /\ \A a \in Acceptor : \E a2 \in Acceptor : f[a2] = a

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsPermutation(f) }

====