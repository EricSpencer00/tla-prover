---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Operators that will be substituted for the corresponding constants in the .cfg
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES Votes, Promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VotePair == [ballot : Ballot, val : Value]

\* Returns the set of votes of acceptor a as a set of <<ballot,value>> pairs
VotesOf(a) == Votes[a]

\* A value v is safe at ballot b if for every lower ballot c there exists a
\* quorum Q such that each member of Q either has already voted for v in c
\* or has promised to a higher ballot than c (and therefore can never vote in c).
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        /\ \A a \in Q :
             ( <<c, v>> \in Votes[a] ) \/ ( Promise[a] > c )

\* A value is chosen if some quorum has all its members vote for it in the same ballot
Chosen == { v \in Value :
               \E b \in Ballot :
                 \E Q \in Quorum :
                   /\ \A a \in Q : <<b, v>> \in Votes[a] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
IncreasePromise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > Promise[a]               \* strictly higher
      /\ Promise' = [Promise EXCEPT ![a] = b]
      /\ UNCHANGED Votes

VoteAction ==
  \E a \in Acceptor :
    \E v \in Value :
      \E b \in Ballot :
        /\ b >= Promise[a]                         \* not below threshold
        /\ ~(\E vv \in Value : <<b, vv>> \in Votes[a])   \* a hasn't voted in b yet
        /\ \A a2 \in Acceptor :
              ( \E vv2 \in Value : <<b, vv2>> \in Votes[a2] ) => vv2 = v
        /\ Safe(v, b)                              \* safety condition
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {<<b, v>>}]
        /\ Promise' = [Promise EXCEPT ![a] = b]
        /\ UNCHANGED << >>

Next == \/ IncreasePromise
        \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Promise>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in Acceptor : Votes[a] \subseteq (Ballot \X Value)
  /\ \A a \in Acceptor : Promise[a] \in Ballot \/ Promise[a] = -1
  /\ \A b \in Ballot :
        (\E a1 \in Acceptor : <<b, v1>> \in Votes[a1]) /\ 
        (\E a2 \in Acceptor : <<b, v2>> \in Votes[a2]) => v1 = v2
        \* the above quantifies over v1, v2 implicitly; we rewrite explicitly:
     \A v1, v2 \in Value :
        ( (\E a1 \in Acceptor : <<b, v1>> \in Votes[a1]) /\ 
          (\E a2 \in Acceptor : <<b, v2>> \in Votes[a2]) ) => v1 = v2
  /\ \A a \in Acceptor :
        \A <<b, v>> \in Votes[a] : Safe(v, b)

\* ----------------------------------------------------------------------
\* Property: at most one value can ever be chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar == 
  \A v1, v2 \in Chosen : v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set (permutations of acceptors)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====