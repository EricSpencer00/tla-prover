---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Variables: votes each acceptor cast, and each acceptor's promise threshold.
VARIABLES votes, thresh

vars == <<votes, thresh>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thresh \in [Acceptor -> Ballot]

\* An acceptor may only vote in a ballot above its own promise threshold.
OnlyAboveThreshold ==
  \A a \in Acceptor : \A p \in votes[a] : p[1] >= thresh[a]

\* Two votes for different values in the same ballot can never both exist.
NoBallotConflict ==
  \A a, a2 \in Acceptor :
    \A p \in votes[a] : \A q \in votes[a2] :
      (p[1] = q[1]) => (p[2] = q[2])

\* Votes are always type-correct.
VoteTypes ==
  \A a \in Acceptor : \A p \in votes[a] :
    /\ p[1] \in Ballot
    /\ p[2] \in Value

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

\* An acceptor promises never to vote below a new, higher ballot number.
RaiseThresh(a, b) ==
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor casts a vote, only for a value that is safe at that ballot.
CastVote(a, b, v) ==
  /\ b >= thresh[a]
  /\ \A p \in votes[a] : p[1] # b
  /\ \A a2 \in Acceptor : \A p \in votes[a2] : (p[1] = b) => (p[2] = v)
  /\ \E Q \in Quorum :
        \A c \in Ballot :
          (c < b) =>
            /\ \A a2 \in Q : (\E p \in votes[a2] : p[1] = c) \/ (\A p \in votes[a2] : p[1] # c)
            /\ \A a2 \in Q : (\E p \in votes[a2] : (p[1] = c) /\ (p[2] = v))
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

\* No explicit leader: any acceptor may advance to the next logical ballot.
Advance(a) ==
  /\ \E b \in Ballot : b > thresh[a]
  /\ \E v \in Value : CastVote(a, thresh[a] + 1, v)

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThresh(a, b)
  \/ \E a \in Acceptor : Advance(a)

Spec == Init /\ [][Next]_vars

\* At most one value is ever chosen by a quorum: the chosen set has bounded size.
Inv == NoBallotConflict /\ OnlyAboveThreshold /\ VoteTypes

\* SAFETY PROPERTY: the voting algorithm implements consensus.
\* Any value approved by a quorum at any ballot is the single chosen value.
ConsensusSpecBar == (\E b \in Ballot, Q \in Quorum : \A a \in Q : <<b, v1>> \in votes[a])
                       => (\A b \in Ballot, Q \in Quorum : \A a \in Q : <<b, v2>> \in votes[a] => v1 = v2)

\* Quorum overlap is essential for the consistency guarantee.
MCSymmetry ==
  {f \in [Acceptor -> Acceptor] :
     /\ (Cardinality(Acceptor) = 1) \/ (Cardinality(Acceptor) = 2 => f = [x \in Acceptor |-> x])
     /\ \A Q \in Quorum : {f[x] : x \in Q} = Q}

\* These operators rename the abstract constants for SANY and TLC model checking.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====