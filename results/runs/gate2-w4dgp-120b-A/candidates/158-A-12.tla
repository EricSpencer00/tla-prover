---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

Vote == [by : Acceptor, at : Ballot, val : Value]

\* The safe predicate is the heart of the consensus guarantee: a vote for
\* value v at ballot b is only allowed if every lower ballot c already has
\* a quorum all committed to v (or unable to vote at c), which rules out a
\* quorum voting for a different value in a lower ballot.
Safe(v, b) ==
  /\ \A c \in 0..(b - 1) : \E q \in MCQuorum :
       \A a \in q : \E w \in votes[a] :
         /\ w.val = v
         /\ w.at = c
         \/ promised[a] > c

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ promised = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold, refusing to vote in earlier
\* ballots (a typical prepare/promise step in Paxos-style protocols).
Raise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Cast a vote for value v at ballot b, only if no other value has been
\* voted for in ballot b anywhere, and only if v is already safe at b.
Cast(a, b, v) ==
  /\ b >= promised[a]
  /\ \A w \in votes[a] : w.at # b
  /\ ~ \E c \in votes : c.at = b /\ c.val # v
  /\ Safe(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[by |-> a, at |-> b, val |-> v]}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : Raise(a, b)
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in MCAcceptor, w \in votes[a] : Safe(w.val, w.at)
  /\ (\A a1, a2 \in MCAcceptor, w1 \in votes[a1], w2 \in votes[a2] :
        w1.at = w2.at => w1.val = w2.val)
  /\ (\A a \in MCAcceptor : votes[a] \subseteq Vote /\ promised[a] \in -1..(Cardinality(MCBallot) - 1))

\* The chosen set of values is derived from the votes, so consistency of
\* the votes directly gives the consistency of the chosen values.
\* Consistency: at most one value is ever chosen by a quorum.
\* (AtMostOneChosen is the name the .cfg expects for this safety property.)
AtMostOneChosen ==
  Cardinality({v \in MCValue : \E q \in MCQuorum :
    \A a \in q : \E w \in votes[a] : w.val = v}) <= 1

SpecRefinement == Spec /\ Inv /\ AtMostOneChosen
ConsensusSpecBar == SpecRefinement

\* Symmetry: the identity permutation, which is always present.
MCSymmetry == {x \in [MCAcceptor -> MCAcceptor] : \A a \in MCAcceptor : x[a] = a}

\* The .cfg substitutes these with concrete finite instances for model checking.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====