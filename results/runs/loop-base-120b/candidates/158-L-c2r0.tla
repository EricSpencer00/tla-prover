---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Substitution operators required by the configuration
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, thresh

\* A vote is a record with fields ballot ∈ Ballot and value ∈ Value
Vote == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all ballots strictly lower than b
LowerBallots(b) == { c \in Ballot : c < b }

\* An acceptor a can never vote in ballot c iff its threshold is already > c
NeverCanVote(a, c) == thresh[a] > c

\* Whether acceptor a has already voted for value v in ballot b
HasVote(a, b, v) ==
  \E vt \in votes[a] : vt.ballot = b /\ vt.value = v

\* Whether acceptor a has voted for any value (different from v) in ballot b
HasOtherVote(a, b, v) ==
  \E vt \in votes[a] : vt.ballot = b /\ vt.value # v

\* Safety of a value at a given ballot
SafeValue(v, b) ==
  \A c \in LowerBallots(b) :
    \E Q \in Quorum :
      \A a \in Q :
        ( HasVote(a, c, v) \/ NeverCanVote(a, c) )

\* At most one value is voted for in a given ballot across all acceptors
OneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : HasVote(a1, b, v1)) /\ 
        (\E a2 \in Acceptor : HasVote(a2, b, v2)) ) => v1 = v2

\* Every vote in the system is safe
AllVotesSafe ==
  \A a \in Acceptor :
    \A vt \in votes[a] :
      SafeValue(vt.value, vt.ballot)

\* Type correctness of thresholds (allow -1 as “no promise”)
ThreshTypeCorrect ==
  \A a \in Acceptor : thresh[a] \in (Ballot \cup {-1})

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Promise: an acceptor raises its threshold without voting
Promise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > thresh[a]               \* strictly higher than current threshold
      /\ votes' = votes
      /\ thresh' = [thresh EXCEPT ![a] = b]

\* Vote: an acceptor casts a vote for value v in ballot b
VoteAction ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= thresh[a]                         \* not below current promise
        /\ ~(\E vt \in votes[a] : vt.ballot = b)  \* no prior vote in this ballot
        /\ \A a2 \in Acceptor :
              ( HasOtherVote(a2, b, v) => FALSE ) \* no other vote for a different value
        /\ SafeValue(v, b)                         \* safety condition
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
        /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ Promise
  \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv == /\ AllVotesSafe
       /\ OneValuePerBallot
       /\ ThreshTypeCorrect

\* ----------------------------------------------------------------------
\* Safety property: at most one value can be chosen
\* ----------------------------------------------------------------------
ChosenInBallot(v, b) ==
  \E Q \in Quorum :
    \A a \in Q :
      HasVote(a, b, v)

ConsensusSpecBar ==
  \A v1, v2 \in Value, b1, b2 \in Ballot :
    ( ChosenInBallot(v1, b1) /\ ChosenInBallot(v2, b2) ) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (identity permutation only)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====