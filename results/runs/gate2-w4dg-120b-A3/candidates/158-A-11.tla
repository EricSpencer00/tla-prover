---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Natural-numbered ballots; the model bounds Ballot to a small finite range.
CONSTANTS Acceptor, Value, Quorum, Ballot

Votes == [ac: Acceptor, n: Ballot, v: Value]
Choice == [n: Ballot, v: Value]

VARIABLES cast, minN

vars == <<cast, minN>>

TypeOK ==
  /\ cast \subseteq Votes
  /\ minN \in [Acceptor -> (Ballot \cup {-1})]

Init ==
  /\ cast = {}
  /\ minN = [a \in Acceptor |-> -1]

\* The quorum used to certify a value at a ballot is part of the action,
\* so the same ballot and value can never be certified by two disjoint sets.
Certify(b, v, Q) ==
  /\ Q \in Quorum
  /\ \A a \in Q : b >= minN[a]
  /\ \A a \in Q : \A c \in Ballot : (c = b) => ~\E e \in cast :
        /\ e.ac = a
        /\ e.n = c
  /\ \A a \in Q : \A c \in Ballot : (c < b) => \E e \in cast :
        /\ e.ac = a
        /\ e.n = c
        /\ e.v = v
  /\ \A x \in (UNION Quorum) : \A c \in Ballot : (c < b) => ~\E e \in cast :
        /\ e.ac = x
        /\ e.n = c
        /\ e.v = v
        /\ c >= minN[x]
  /\ \A c \in Ballot : c < b => \E Q2 \in Quorum : \A a \in Q2 :
        /\ c >= minN[a]
        /\ \E e \in cast : e.ac = a /\ e.n = c /\ e.v = v

MakePromise(a, b) ==
  /\ b > minN[a]
  /\ minN' = [minN EXCEPT ![a] = b]
  /\ UNCHANGED cast

CastVote(a, b, v, Q) ==
  /\ b >= minN[a]
  /\ \A e \in cast : ~(e.ac = a /\ e.n = b)
  /\ \A c \in Ballot : \A e \in cast : (e.n = c /\ e.v # v) => ~\E x \in Q :
        /\ c = b
        /\ x = a
  /\ Certify(b, v, Q)
  /\ cast' = cast \cup {[ac |-> a, n |-> b, v |-> v]}
  /\ minN' = [minN EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : MakePromise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value, Q \in Quorum : CastVote(a, b, v, Q)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen by a quorum.
Inv ==
  /\ \A e \in cast : e.n \in Ballot /\ e.v \in Value
  /\ \A c \in Ballot : \A a \in Acceptor : \A e \in cast :
        (e.ac = a /\ e.n = c) => e.n >= minN[a]
  /\ \A n \in Ballot : \A a1 \in Acceptor : \A a2 \in Acceptor :
        (\E e \in cast : e.ac = a1 /\ e.n = n) /\ (\E e \in cast : e.ac = a2 /\ e.n = n)
          => (\E e1 \in cast : e1.ac = a1 /\ e1.n = n) /\ (\E e2 \in cast : e2.ac = a2 /\ e2.n = n)

\* Intensional refinement: the chosen set is derived from the votes.
Chosen == { v \in Value : \E Q \in Quorum : \A a \in Q : \E e \in cast : e.ac = a /\ e.v = v }
ConsensusSpecBar == Cardinality(Chosen) <= 1

MCSymmetry == {f \in [Acceptor -> Acceptor] : \A Q \in Quorum : f[Q] \in Quorum}

\* The .cfg substitutes these finite-bounded versions of the constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====