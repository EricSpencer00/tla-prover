---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

\* ----------------------------------------------------------------------
\* Derived constant definitions (for readability)
\* ----------------------------------------------------------------------
Quorums == Quorum

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == [bal : Ballot, val : Value]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES votes, thresh

\* votes[acc] is the set of votes cast by acceptor acc
\* thresh[acc] is the current promise threshold of acceptor acc
vars == << votes, thresh >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
InitVotes == [acc \in Acceptor |-> {}]
InitThresh == [acc \in Acceptor |-> -1]

\* A quorum q is safe for value v at ballot b if for every lower ballot c
\* there exists a quorum in which each member either has already voted for v
\* at c or cannot vote at c (its threshold already exceeds c).
SafeAt(v, b) ==
  \A c \in Ballot : c < b =>
    \E q \in Quorums :
      \A a \in q :
        ( [bal |-> c, val |-> v] \in votes[a] ) \/ ( thresh[a] > c )

\* The set of chosen values (those with a quorum of votes in the same ballot)
Chosen == 
  { v \in Value :
      \E b \in Ballot :
        \E q \in Quorums :
          \A a \in q : [bal |-> b, val |-> v] \in votes[a] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = InitVotes
  /\ thresh = InitThresh

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase promise threshold without voting
IncreaseThresh ==
  \E acc \in Acceptor :
    \E new \in Ballot :
      /\ new > thresh[acc]
      /\ thresh' = [thresh EXCEPT ![acc] = new]
      /\ UNCHANGED votes

\* 2. Cast a vote for a value in a ballot
VoteAction ==
  \E acc \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= thresh[acc]
        /\ [bal |-> b, val |-> v] \notin votes[acc]
        /\ \A a \in Acceptor :
             ( [bal |-> b, val |-> v] \in votes[a] ) => v = v  \* trivial, keeps type
        /\ \A a \in Acceptor :
             ( [bal |-> b, val |-> v'] \in votes[a] ) =>
               v' = v
        /\ \E q \in Quorums :
             \A a \in q : [bal |-> b, val |-> v] \in votes[a] \/ (thresh[a] > b)
        /\ votes' = [votes EXCEPT ![acc] = votes[acc] \cup { [bal |-> b, val |-> v] }]
        /\ thresh' = [thresh EXCEPT ![acc] = b]
        /\ UNCHANGED << >>

\* 3. Stutter (to avoid deadlock)
Stutter == UNCHANGED vars

Next == 
  \/ IncreaseThresh
  \/ VoteAction
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the cfg
\* ----------------------------------------------------------------------
\* (a) Every vote is safe at its ballot
\* (b) At most one value per ballot across all acceptors
\* (c) Type correctness (ensured by construction)
Inv ==
  /\ \A acc \in Acceptor :
        \A vt \in votes[acc] :
          SafeAt(vt.val, vt.bal)
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( \E acc \in Acceptor : [bal |-> b, val |-> v1] \in votes[acc] ) /\
          ( \E acc \in Acceptor : [bal |-> b, val |-> v2] \in votes[acc] )
          => v1 = v2

\* ----------------------------------------------------------------------
\* Property required by the cfg
\* ----------------------------------------------------------------------
ConsensusSpecBar == Cardinality(Chosen) <= 1

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

=================================