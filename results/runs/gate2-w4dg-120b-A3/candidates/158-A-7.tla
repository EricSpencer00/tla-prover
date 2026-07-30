---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == {Qu1, Qu2, Qu3}
Ballot == {0, 1, 2}

\* Quorum membership: a finite, overlapping family of acceptor sets.
Members(Qu1) == {a1, a2}
Members(Qu2) == {a2, a3}
Members(Qu3) == {a1, a3}

\* Bounded versions of the unbounded sets, used by the .cfg substitutions.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A vote is a ballot number paired with a chosen value.
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

\* A value v is safe at ballot b if every lower ballot c already had a
\* unanimous supporting quorum for v or is unwinnable.
SafeAt(vb) ==
  /\ \E q \in Quorum : \A a \in Members(q) : <<vb.ballot, v>> \in votes[a]
  /\ \A c \in Ballot :
       c < vb.ballot =>
         \/ \E q \in Quorum : \A a \in Members(q) : <<c, v>> \in votes[a]
         \/ \A a \in Acceptor : c \notin {x.ballot : x \in votes[a]}

\* Every vote that has been cast was safe at the ballot it was cast in.
VotesAreSafe ==
  \A a \in Acceptor, x \in votes[a] : SafeAt(x)

\* No ballot ever carries votes for two different values.
OneValuePerBallot ==
  \A a1 \in Acceptor, a2 \in Acceptor, x \in votes[a1], y \in votes[a2] :
     x.ballot = y.ballot => x.value = y.value

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold so it will not vote below it.
Raise ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot that passes the four checks.
Cast ==
  \E a \in Acceptor, v \in Value, b \in Ballot :
    /\ b >= threshold[a]
    /\ \A x \in votes[a] : x.ballot # b
    /\ \A a2 \in Acceptor, x \in votes[a2] : x.ballot = b => x.value = v
    /\ SafeAt([ballot |-> b, value |-> v])
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[ballot |-> b, value |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next == Raise \/ Cast

Spec == Init /\ [][Next]_vars

\* A chosen value is one that some quorum has unanimously voted for.
Chosen == {v \in Value :
  \E q \in Quorum : \A a \in Members(q) : \E x \in votes[a] : x.value = v}

Inv == TypeOK /\ VotesAreSafe /\ OneValuePerBallot

\* Consistency: at most one value is ever chosen across all quorums.
ConsensusSpecBar == Cardinality(Chosen) <= 1

\* The permutation swapping a1 and a2, fixing a3, is a symmetry of the
\* acceptor set that must preserve the specification.
MCSymmetry == {f \in [Acceptor -> Acceptor] : f[a1] = a2 /\ f[a2] = a1 /\ f[a3] = a3}

====