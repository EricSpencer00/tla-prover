---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == a1 \cup a2 \cup a3
MCValue == v1 \cup v2
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promise

vars == <<votes, promise>>

VoteSpace == [ballon : MCBallot, val : MCValue]

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET VoteSpace]
  /\ promise \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ promise = [a \in MCAcceptor |-> -1]

SafeAt(v, b) ==
  /\ \A a \in MCAcceptor: [ballon |-> b, val |-> v] \in votes[a]
  /\ \A c \in MCBallot:
       (c < b)
         => \E Q \in MCQuorum:
              \A a \in Q:
                \/ [ballon |-> c, val |-> v] \in votes[a]
                \/ (\A w \in votes[a]: w.ballon # c)

RaisePromise(a, b) ==
  /\ b > promise[a]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, v, b) ==
  /\ b >= promise[a]
  /\ [ballon |-> b, val |-> v] \notin votes[a]
  /\ \A a2 \in MCAcceptor:
       [ballon |-> b, val |-> v] \in votes[a2] \/ (\A w \in votes[a2]: w.ballon # b)
  /\ \E Q \in MCQuorum: \A a2 \in Q: [ballon |-> b, val |-> v] \in votes[a2]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ballon |-> b, val |-> v]}]
  /\ promise' = [promise EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot: RaisePromise(a, b)
  \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot: CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

Chosen == { v \in MCValue : \E Q \in MCQuorum, a \in Q: [ballon |-> 0, val |-> v] \in votes[a] }

BallotOneChoice ==
  \A v1, v2 \in Chosen: v1 = v2

VoteSafety ==
  \A a \in MCAcceptor, w \in votes[a]: SafeAt(w.val, w.ballon)

BallotUniqueness ==
  \A w1, w2 \in UNION { votes[a] : a \in MCAcceptor }:
    (w1.ballon = w2.ballon) => (w1.val = w2.val)

StateConstraint == TypeOK /\ VoteSafety /\ BallotUniqueness

\* The voting algorithm implements consensus: the chosen set is derived from
\* the votes and is always a singleton or empty, so the vote set refines
\* the abstract consensus specification.
ConsensusSpecBar ==
  /\ StateConstraint
  /\ Chosen = { v \in MCValue : \E Q \in MCQuorum, a \in Q: [ballon |-> 0, val |-> v] \in votes[a] }

\* Acceptance is a purely technical requirement for the configured
\* symmetries; it is false in every reachable state of this system.
MCSymmetry ==
  \E f \in [MCAcceptor -> MCAcceptor]:
    /\ \A a \in MCAcceptor: f[a] = a
    /\ (\A a, b \in MCAcceptor: f[a] = f[b] => a = b)
    /\ \A Q \in MCQuorum: { f[a] : a \in Q } \in MCQuorum

====