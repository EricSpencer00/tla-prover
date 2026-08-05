---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* The abstract type-casting operators below let the .cfg file rename the
\* Acceptor/Value/Quorum/Ballot constants without also renaming every
\* occurrence of those names throughout the module body.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* A vote is a ballot-number/value pair; a quorum names a set of acceptors
\* and is drawn from the constant MCQuorum.  A value is chosen when a
\* quorum has all of its members vote for it in some ballot, and because
\* quorums overlap and votes are cast only when safe under that same
\* overlap, two quorums can never settle on different values.

VARIABLES votes, thr

vars == << votes, thr >>

VoteRec == [ball : MCBallot, val : MCValue]
NoVote == [ball |-> 0, val |-> CHOOSE v \in MCValue : TRUE]

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET [ball : MCBallot, val : MCValue]]
  /\ thr \in [MCAcceptor -> -1..(Cardinality(MCBallot) - 1)]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ thr = [a \in MCAcceptor |-> -1]

\* The ballot promised is the highest ballot the acceptor has committed to
\* voting in; it can only move upward, never backward.
TotalPromising(a, b) ==
  /\ thr[a] >= 0
  /\ b \in MCQuorum
  /\ a \in b
  /\ (IF thr[a] < b THEN thr[a] + 1 ELSE thr[a]) <= ThrMax

Promising(a, b) ==
  /\ TotalPromising(a, b)
  /\ thr' = [thr EXCEPT ![a] = (IF thr[a] < b THEN thr[a] + 1 ELSE thr[a])]
  /\ UNCHANGED votes

\* A vote may be cast at ballot c only if no other acceptor has already
\* voted for a different value at that ballot, and only if the value is
\* safe at c -- that is, every lower ballot is already backed by a quorum
\* for that value or is dead to every acceptor that can still vote.
SafeAt(a, c) ==
  /\ \A b \in MCBallot, z \in MCValue :
       [ball |-> b, val |-> z] \in votes[a] => b <= c
  /\ \A b \in 0..(c - 1), z \in MCValue :
       (([ball |-> b, val |-> z] \in votes[a]) \/ (b < thr[a]))
         =>
         \E q \in MCQuorum :
           /\ a \in q
           /\ \A y \in q :
                ([ball |-> b, val |-> z] \in votes[y]) \/ (b < thr[y])

\* Casting a vote also moves the acceptor's threshold up to its ballot.
Casting(a, c, v) ==
  /\ c >= thr[a]
  /\ [ball |-> c, val |-> v] \notin votes[a]
  /\ \A x \in MCAcceptor : [ball |-> c, val |-> v] \notin votes[x]
  /\ \E q \in MCQuorum :
       /\ a \in q
       /\ \A y \in q : SafeAt(y, c)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> c, val |-> v]}]
  /\ thr' = [thr EXCEPT ![a] = c]
  /\ UNCHANGED << >>

Next == \E a \in MCAcceptor :
          \/ \E b \in MCQuorum : Promising(a, b)
          \/ \E c \in MCBallot, v \in MCValue : Casting(a, c, v)

\* The quorum-overlap property assumed here (any two quorums intersect)
\* is what makes the ballot/base-value test in SafeAt cut the damage:
\* Cast votes are always safe at their own ballot, so any two quorums
\* agreeing on a ballot must agree on the value, and a quorum in the
\* next ballot can only be built on the value already settled at the
\* previous one.
QuorumOverlap ==
  \A p, q \in MCQuorum : p # q => p \cap q # {}

QuorumVoted(v) == \E q \in MCQuorum : \A a \in q : [ball |-> 0, val |-> v] \in votes[a]

VoteCastSafe ==
  \A a \in MCAcceptor : \A r \in votes[a] : SafeAt(a, r.ball)

OnlyOneValuePerBallot ==
  \A c \in MCBallot, v1, v2 \in MCValue :
       (\A a \in MCAcceptor : [ball |-> c, val |-> v1] \in votes[a]
            \/ [ball |-> c, val |-> v2] \in votes[a])
         => v1 = v2

TypeOKInv == TypeOK /\ QuorumOverlap

Inv ==
  /\ VoteCastSafe
  /\ OnlyOneValuePerBallot
  /\ TypeOKInv

\* The Voting: SPECIFICATION section below implements exactly the
\* abstract consensus spec named ConsensusSpecBar in the accompanying
\* consensus specification module, with the chosen set derived from
\* the votes.  The refinement mapping extracts the set of quorum-backed
\* values from the concrete voting state.
TypeOKRec ==
  /\ votes \in [MCAcceptor -> SUBSET [ball : MCBallot, val : MCValue]]
  /\ thr \in [MCAcceptor -> (-1)..(Cardinality(MCBallot) - 1)]

\* The chosen set is built from the votes rather than a separate
\* register, so no action ever writes it directly.
Chosen == {v \in MCValue : QuorumVoted(v)}

RecurChoice ==
  /\ \E c \in MCBallot, q \in MCQuorum, v \in MCValue :
       \A a \in q : [ball |-> c, val |-> v] \in votes[a]
  /\ /\ Cardinality(Chosen) <= 1
       /\ \A c \in MCBallot, v1, v2 \in MCValue :
            (\A a \in MCAcceptor : [ball |-> c, val |-> v1] \in votes[a]
                 \/ [ball |-> c, val |-> v2] \in votes[a])
              => v1 = v2
       /\ \A a \in MCAcceptor, r \in votes[a] : SafeAt(a, r.ball)
  /\ TypeOKRec

InitRec ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ thr = [a \in MCAcceptor |-> -1]

Spec == Init /\ [][Next]_vars
ConsensusSpecBar == InitRec /\ [][RecurChoice]_vars

\* Symmetry: every permutation of acceptors is a semantic automorphism
\* of the voting process, because acceptors are indistinguishable except
\* for the votes they happen to hold.
MCSymmetry ==
  {f \in [MCAcceptor -> MCAcceptor] :
     \A a \in MCAcceptor : [ball |-> 0, val |-> v1] \in votes[f[a]]
       => [ball |-> 0, val |-> v1] \in votes[a]
     /\ \A b \in MCQuorum : f[b] \in MCQuorum}

====