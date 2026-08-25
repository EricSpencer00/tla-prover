---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\*  Derived constants for model checking (overridden by the .cfg file)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ Votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ Threshold \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\*  Safety of a value at a ballot
\* ----------------------------------------------------------------------
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        \A a \in q :
          (<<c, v>> \in Votes[a]) \/ (Threshold[a] > c)

\* ----------------------------------------------------------------------
\*  Invariant that every cast vote is safe and at most one value per ballot
\* ----------------------------------------------------------------------
SafeInvariant ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      LET b   == vote[1] IN
      LET val == vote[2] IN
        Safe(val, b)

OneValuePerBallot ==
  \A b \in Ballot :
    \A aA, aB \in Acceptor :
      \A valA, valB \in Value :
        (<<b, valA>> \in Votes[aA] /\ <<b, valB>> \in Votes[aB]) => valA = valB

Inv == /\ TypeInvariant
       /\ SafeInvariant
       /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
PromiseIncrease ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > Threshold[a]
    /\ UNCHANGED Votes
    /\ Threshold' = [Threshold EXCEPT ![a] = b]

Vote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= Threshold[a]
    /\ \A vPrime \in Value : <<b, vPrime>> \notin Votes[a]          \* a has not voted in ballot b yet
    /\ \A aPrime \in Acceptor :
          \A vPrime \in Value :
            (<<b, vPrime>> \in Votes[aPrime]) => vPrime = v       \* at most one value per ballot
    /\ Safe(v, b)
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {<<b, v>>}]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next == \/ PromiseIncrease \/ Vote

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\*  Consensus property: at most one chosen value
\* ----------------------------------------------------------------------
Chosen(v) ==
  \E b \in Ballot, q \in Quorum :
    /\ \A a \in q : <<b, v>> \in Votes[a]

ConsensusSpecBar ==
  \A valA, valB \in Value :
    (Chosen(valA) /\ Chosen(valB)) => valA = valB

\* ----------------------------------------------------------------------
\*  Symmetry definition (identity permutation suffices)
\* ----------------------------------------------------------------------
IsBijective(f) ==
  /\ \A x, y \in Acceptor : f[x] = f[y] => x = y
  /\ \A z \in Acceptor : \E x \in Acceptor : f[x] = z

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsBijective(f) }

=============================================================================