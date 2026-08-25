---- MODULE Voting ----
\*=====================================================================
\* Constants (instantiated in the .cfg file)
\*=====================================================================
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*=====================================================================
\* Operators that the .cfg substitutes (may be bounded versions)
\*=====================================================================
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES votes, threshold

\*=====================================================================
\* Helper definitions
\*=====================================================================
\* A vote is a pair <<ballot, value>>
VotePair == [ballot : Ballot, value : Value]

\* Whether acceptor a has already voted in ballot b
VotedIn(a, b) == \E <<bb, vv>> \in votes[a] : bb = b

\* Safety of a value v at ballot b:
\* for every lower ballot c there exists a quorum Q such that
\* each member of Q either already voted for v in c or will never
\* vote in c (its promise threshold exceeds c).
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

\* A value is chosen if some quorum has all its members voting for it
\* in the same ballot.
Chosen(v) ==
  \E b \in Ballot :
    \E Q \in Quorum :
      \A a \in Q : <<b, v>> \in votes[a]

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\*=====================================================================
\* Actions
\*=====================================================================
\* 1. Promise – increase an acceptor's threshold without voting
Promise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > threshold[a]
      /\ threshold' = [threshold EXCEPT ![a] = b]
      /\ votes' = votes

\* 2. Vote – cast a vote for value v in ballot b
Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= threshold[a]
        /\ ~VotedIn(a, b)
        /\ \A a2 \in Acceptor :
             a2 # a =>
               \A <<bb, vv>> \in votes[a2] :
                 (bb = b) => (vv = v)
        /\ Safe(v, b)
        /\ threshold' = [threshold EXCEPT ![a] = b]
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]

Next == Promise \/ Vote

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<votes, threshold>>

\*=====================================================================
\* Invariant
\*=====================================================================
Inv ==
  /\ \A a \in Acceptor :
        \A <<b, v>> \in votes[a] : Safe(v, b)
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1])
            /\ (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) )
          => v1 = v2
  /\ \A a \in Acceptor :
        threshold[a] = -1 \/ threshold[a] \in Ballot

\*=====================================================================
\* Property: at most one value can ever be chosen
\*=====================================================================
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\*=====================================================================
\* Symmetry definition (set of permutations over Acceptor)
\*=====================================================================
MCSymmetry == {
    [a \in Acceptor |-> a] \* identity permutation (can be extended)
  }

\*=====================================================================
\* Assumption: quorum overlap
\*=====================================================================
ASSUME QuorumOverlap ==
  \A Q1, Q2 \in Quorum :
    (Q1 # Q2) => (Q1 \cap Q2) # {}

=============================================================================