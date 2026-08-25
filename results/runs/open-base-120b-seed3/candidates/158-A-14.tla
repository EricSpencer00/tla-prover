---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* -------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* -------------------------------------------------
\* Operators required by the configuration
\* -------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* -------------------------------------------------
\* Symmetry set (identity permutation is always a symmetry)
\* -------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES Votes, Threshold

\* Votes[a] is the set of votes cast by acceptor a.
\* Each vote is a record [ballot : Ballot, value : Value].
\* Threshold[a] is the minimal ballot number at which a
\* may vote (initially -1, meaning no promise made).
\* -------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Vote == [ballot : Ballot, value : Value]

\* The set of ballots that are strictly lower than b
LowerBallots(b) == { c \in Ballot : c < b }

\* A value v is safe at ballot b iff for every lower ballot c
\* there exists a quorum in which each member has either
\* already voted for v in c or can never vote in c
\* (i.e., its threshold is greater than c).
Safe(v, b) ==
  \A c \in LowerBallots(b) :
    \E q \in Quorum :
      \A a \in q :
        ( \E vote \in Votes[a] : vote.ballot = c /\ vote.value = v )
        \/ ( Threshold[a] > c )

\* No acceptor has voted for two different values in the same ballot
AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      \A v1, v2 \in Value :
        ( [ballot |-> b, value |-> v1] \in Votes[a1]
          /\ [ballot |-> b, value |-> v2] \in Votes[a2] )
        => v1 = v2

\* Every vote that appears in the state is safe
AllVotesSafe ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      Safe(vote.value, vote.ballot)

\* Type correctness of the variables
TypeCorrect ==
  /\ Votes \in [Acceptor -> SUBSET Vote]
  /\ Threshold \in [Acceptor -> Int]

\* The global invariant
Inv == TypeCorrect /\ AtMostOneValuePerBallot /\ AllVotesSafe

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
\* (1) An acceptor may raise its promise threshold
IncreasePromise ==
  \E a \in Acceptor :
    \E newB \in Ballot :
      /\ newB > Threshold[a]          \* strictly higher
      /\ Threshold' = [Threshold EXCEPT ![a] = newB]
      /\ Votes' = Votes

\* (2) An acceptor may cast a vote for a value in a ballot
CastVote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= Threshold[a]                      \* not below current promise
        /\ \A vote \in Votes[a] : vote.ballot # b   \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
            \A vote2 \in Votes[a2] :
              (vote2.ballot = b) => vote2.value = v   \* no different value in same ballot
        /\ Safe(v, b)                              \* safety condition
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next ==
  \/ IncreasePromise
  \/ CastVote

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec ==
  Init /\ [][Next]_<<Votes, Threshold>>

\* -------------------------------------------------
\* Property required by the configuration
\* -------------------------------------------------
ConsensusSpecBar == []Inv

====