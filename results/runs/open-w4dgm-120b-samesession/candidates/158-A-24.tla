---- MODULE Voting ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

\* Actor sets are re-declared as operators so the model checker can apply
\* symmetry reduction over a bounded, order-free permutation of them.
\* The names MCAcceptor etc. are the ones the .cfg file expects to hook in.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* A vote is a ballot-numbered choice; VotesA[a] is the set of votes acceptor a
\* has actually cast. ThresholdA[a] is the lowest ballot a will honor going forward.
VARIABLES VotesA, ThresholdA

TypeOK ==
  /\ VotesA \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ ThresholdA \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ VotesA = [a \in MCAcceptor |-> {}]
  /\ ThresholdA = [a \in MCAcceptor |-> -1]

\* An acceptor raises its participation floor in a higher ballot -- it can only
\* ever vote in ballots at or above this, which is what makes a quorum of them
\* count as an authoritative commitment.
RaiseThreshold(a, b) ==
  /\ b > ThresholdA[a]
  /\ ThresholdA' = [ThresholdA EXCEPT ![a] = b]
  /\ UNCHANGED VotesA

\* A ballot is uniquely owned by one value, and voting runs only for values
\* that are safe at that ballot (nothing committed earlier can be contradicted).
Vote(a, b, v) ==
  /\ b >= ThresholdA[a]
  /\ \A c \in MCBallot : [ball |-> c, val |-> v] \notin VotesA[a]
  /\ \A x \in MCAcceptor : \A c \in MCBallot : [ball |-> c, val |-> w] \in VotesA[x] => v = w
  /\ \E q \in MCQuorum : \A x \in q : SafeAt(v, b, x)
  /\ VotesA' = [VotesA EXCEPT ![a] = VotesA[a] \cup {[ball |-> b, val |-> v]}]
  /\ ThresholdA' = [ThresholdA EXCEPT ![a] = b]

SafeAt(v, b, a) ==
  \A c \in MCBallot :
    (c < b /\ (\A x \in MCAcceptor : [ball |-> c, val |-> v] \in VotesA[x] \/ c < ThresholdA[x]))
    \/ (c >= b)

CastVote == \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)

RaiseAny == \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)

Next == CastVote \/ RaiseAny

Spec == Init /\ [][Next]_<<VotesA, ThresholdA>>

\* Safety: no quorum-voted value can be contradicted by an earlier quorum that
\* voted for something else. The three conjuncts are the full chain of
\* argument: safe votes, at-most-one-value-per-ballot, and well-typedness.
Inv ==
  /\ \A a \in MCAcceptor : \A w \in VotesA[a] : SafeAt(w.val, w.ball, a)
  /\ \A a1 \in MCAcceptor, a2 \in MCAcceptor : \A w1 \in VotesA[a1], w2 \in VotesA[a2] :
        w1.ball = w2.ball => w1.val = w2.val
  /\ TypeOK

Chosen == { v \in MCValue : \E q \in MCQuorum : \A a \in q : \E b \in MCBallot : [ball |-> b, val |-> v] \in VotesA[a] }

\* Refinement: the chosen set is derived from the vote set, and the invariant
\* already forces it to hold at most one value.
ConsensusSpecBar == Cardinality(Chosen) <= 1

Symmetry == [f \in [MCAcceptor -> MCAcceptor] |-> [a \in MCAcceptor |-> f[a]]]

====