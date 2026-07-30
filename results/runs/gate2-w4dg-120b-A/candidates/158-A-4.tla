---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* A vote is a ballot/value pair; VoteBy tracks votes per acceptor.
Vote == [balloon : Ballot, item : Value]
VoteBy == [Acceptor -> SUBSET Vote]

VARIABLES vote, thr

vars == <<vote, thr>>

\* A vote is safe at its ballot once every lower ballot is backed by a quorum
\* that has already voted for the same value or is permanently silent for it.
Obstructed(v) ==
  \E Q \in Quorum :
    \A r \in Q : \A c \in Ballot :
      (c < v.balloon)
        => (\E e \in Q :
              vote[e] \cap ({[balloon |-> c, item |-> v.item]} \cup
                            {[balloon |-> c, item |-> "none"]}))
  \/ (\A c \in Ballot :
        c < v.balloon
          => \E Q \in Quorum :
               \A r \in Q : vote[r] \cap ({[balloon |-> c, item |-> v.item]} \cup
                                          {[balloon |-> c, item |-> "none"]}))

\* A quorum of acceptors has all voted for the same value at the same ballot.
Backing(v) ==
  \E Q \in Quorum :
    \A r \in Q : [balloon |-> v.balloon, item |-> v.item] \in vote[r]

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ thr = [a \in Acceptor |-> -1]

Promised(a, b) ==
  /\ b > thr[a]
  /\ thr' = [thr EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* A vote may be cast only if it is the first in its ballot, if the acceptor
\* has no conflicting vote below it, and only for a value it can back.
Cast(a, b, v) ==
  /\ b >= thr[a]
  /\ \A w \in vote[a] : w.item # v
  /\ \A c \in Acceptor : [balloon |-> b, item |-> v] \notin vote[c]
  /\ Backing([balloon |-> b, item |-> v])
  /\ vote' = [vote EXCEPT ![a] = @ \cup {[balloon |-> b, item |-> v]}]
  /\ thr' = [thr EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promised(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

\* Chosen values are derived from the vote set, filtered by non-silent value.
Chosen == {v.item : v \in UNION {vote[a] : a \in Acceptor} : v.item # "none"}

\* TypeOK: vote sets contain only proper ballot/value pairs; thresholds stay
\* within the bounded ballot range or remain below the lower bound.
TypeOK ==
  /\ vote \in [Acceptor -> SUBSET [balloon : Ballot, item : Value \cup {"none"}]]
  /\ thr \in [Acceptor -> Ballot \cup {-1}]

\* Every cast vote is safe at its ballot number.
SafeVotes ==
  \A a \in Acceptor : \A v \in vote[a] : Obstructed(v)

\* No ballot ever carries two votes for different values.
Uniqueness ==
  \A a \in Acceptor : \A b \in Acceptor :
    \A e1 \in vote[a] : \A e2 \in vote[b] :
      (e1.balloon = e2.balloon) => (e1.item = e2.item)

\* Inv bundles the invariants needed to prove the chosen set is at most one.
Inv == TypeOK /\ SafeVotes /\ Uniqueness

\* The voting algorithm refines the abstract consensus spec via a mapping: the
\* abstract choice set is derived from the underlying votes, and it stays small.
ConsensusSpecBar ==
  /\ Chosen \subseteq Value
  /\ \A x \in Value, y \in Value :
       ((x \in Chosen) /\ (y \in Chosen)) => (x = y)

====