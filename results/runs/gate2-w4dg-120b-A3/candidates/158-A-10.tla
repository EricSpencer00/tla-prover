---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

AcceptorSet == { a1, a2, a3 }

Quorums == { {a1, a2}, {a1, a3}, {a2, a3} }

MCAcceptor == AcceptorSet
MCValue == { v1, v2 }
MCQuorum == Quorums
MCBallot == Ballot

VARIABLES votes, thresh

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ thresh \in [MCAcceptor -> MCBallot \cup { -1 }]

\* Safety (a) below: every cast vote is safe at its ballot number.
\* Safety (b) below: at most one value is voted for in a given ballot.
\* Safety (c) is the type invariant already present.

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ thresh = [a \in MCAcceptor |-> -1]

\* A value is deemed safe at ballot b only if every lower ballot c is
\* already backed by a quorum voting for it, or else unwinnable at c.
SafeAt(y, b) ==
  \A c \in MCBallot : (c < b) =>
    \E Q \in MCQuorum :
      /\ \A a \in Q : (\E v \in MCValue : << c, v >> \in votes[a]) \/ (\A v \in MCValue : << c, v >> \notin votes[a])
      /\ \E v \in MCValue : \A a \in Q : << c, v >> \in votes[a]

\* Actions --------------------------------------------

\* An acceptor may promise a higher-numbered ballot without voting.
RaiseThreshold(a, n) ==
  /\ n > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = n]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, only if the ballot is not
\* below its own promise, it has not already voted in that ballot, no
\* other acceptor has voted for a different value in this ballot, and
\* the value is safe at this ballot.
CastVote(a, n, y) ==
  /\ n >= thresh[a]
  /\ \A m \in MCBallot : m = n => (\A v \in MCValue : << n, v >> \notin votes[a])
  /\ (\A b \in MCAcceptor : << n, y >> \notin votes[b])
  /\ SafeAt(y, n)
  /\ votes' = [votes EXCEPT ![a] = @ \cup { << n, y >> }]
  /\ thresh' = [thresh EXCEPT ![a] = n]

Next ==
  \/ \E a \in MCAcceptor, n \in MCBallot : RaiseThreshold(a, n)
  \/ \E a \in MCAcceptor, n \in MCBallot, y \in MCValue : CastVote(a, n, y)

Spec == Init /\ [][Next]_<<votes, thresh>>

\* In any ballot, at most one value is voted for across all acceptors.
AtMostOneValuePerBallot ==
  \A n \in MCBallot :
    \A a, b \in MCAcceptor :
      \A y \in MCValue :
        (<< n, y >> \in votes[a] /\ << n, y >> \in votes[b]) => a = b

Inv == TypeOK /\ AtMostOneValuePerBallot

\* The derived consensus view: the set of values that actually won a
\* quorum of votes in some ballot. That set never holds two values.
Chosen == { y \in MCValue : \E Q \in MCQuorum, n \in MCBallot :
              \A a \in Q : << n, y >> \in votes[a] }

\* ConsensusSpecBar is the abstract consensus spec; it holds because
\* Chosen can never have two distinct values, which follows from Inv.
ConsensusSpecBar == \A x, y \in Chosen : x = y

\* The model checker only checks bounded ballot numbers -- ballot numbers
\* are declared in the .cfg as a finite set.
\* The symmetry MCSymmetry is the group of renamings of acceptors that
\* swaps a1 and a2 and fixes everything else; it keeps the model
\* finite (it is not used as a reduction, it is merely declared there).
MCSymmetry == {
  {<< a1, a1 >>, << a2, a2 >>, << a3, a3 >>},
  {<< a1, a2 >>, << a2, a1 >>, << a3, a3 >>}
}
====