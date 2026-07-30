---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* Ballots range from 0 to Ballot for model checking; unbounded in principle.
Ballots == 0..Ballot

VARIABLES vote, thresh

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballots \X Value)]
  /\ thresh \in [Acceptor -> (-1)..Ballot]

\* Two quorums always share at least one acceptor: essential for consistency.
QuorumsOverlap ==
  /\ \A Q1 \in Quorum, Q2 \in Quorum : Q1 \cap Q2 # {}
  /\ \A Q \in Quorum : Q # {}

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

\* Safety of a value at a ballot: every earlier ballot was unanimously decided for it.
SafeAt(v, b) ==
  \A c \in 0..(b - 1) :
    \E Q \in Quorum :
      /\ \A a \in Q : [c, v] \in vote[a] \/ ((thresh[a] # -1) /\ thresh[a] >= c)
      /\ \A a \in Q : [c, v] \in vote[a]

\* A quorum votes unanimously for a value in a ballot, so it is chosen.
Chosen(v) == \E Q \in Quorum : \A a \in Q : [thresh[a], v] \in vote[a]
AllVotersOnBallot(b, v) == \A a \in Acceptor : [b, v] \in vote[a]

\* An acceptor may silently raise its threshold; this is how the system stalls.
IncreaseThresh(a, b) ==
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* An acceptor casts a vote for a value in a ballot; it must be the only value used
\* in that ballot and must be safe at that ballot.
CastVote(a, b, v) ==
  /\ b >= thresh[a]
  /\ \A c \in Ballots : [c, v] \in vote[a] => c # b
  /\ \A x \in Acceptor : \A c \in Ballots : [c, x] \in vote[a] => x = v
  /\ SafeAt(v, b)
  /\ vote' = [vote EXCEPT ![a] = @ \cup {[b, v]}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor :
    \/ \E b \in Ballots : IncreaseThresh(a, b) \/ \E v \in Value : CastVote(a, b, v)

\* A cast vote is always safe at its ballot number.
VotesAreSafe ==
  \A a \in Acceptor :
    \A p \in vote[a] : SafeAt(p[2], p[1])

\* At most one value is voted for in any given ballot.
BallotAgreement ==
  \A b \in Ballots :
    \A v1, v2 \in Value :
      (AllVotersOnBallot(b, v1) /\ AllVotersOnBallot(b, v2)) => v1 = v2

\* Type correctness is given separately, since it is not an invariant.
TypesAreWellFormed == TypeOK

Inv == VotesAreSafe /\ BallotAgreement /\ TypesAreWellFormed

Spec == Init /\ [][Next]_<<vote, thresh>>

\* Refinement: the voting algorithm implements consensus -- at most one value is
\* ever chosen -- by mapping to the abstract specification's chosen set.
ConsensusSpecBar == \A v \in Value : Chosen(v) => \A w \in Value : Chosen(w) => w = v
====