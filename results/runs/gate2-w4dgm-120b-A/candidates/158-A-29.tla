---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME Acceptor = {a1, a2, a3}
ASSUME Value = {v1, v2}
ASSUME MCBallot \subseteq Ballot
ASSUME a1 \notin MCBallot
ASSUME MCBallot # {}
ASSUME MCSymmetry = {f \in [Acceptor -> Acceptor] :
  \A x1 \in Acceptor, x2 \in Acceptor : x1 = x2 <=> f[x1] = f[x2]}

VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (-1..(Cardinality(Ballot)))]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor raises its threshold and refuses to vote below it.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Consensus(a, b, v) ==
  /\ b \notin MCBallot
  /\ b \notin {c \in Ballot : \E x \in Acceptor : <<c, v>> \in votes[x]}
  /\ b >= threshold[a]
  /\ \A x \in Acceptor : <<b, v>> \notin votes[x]
  /\ \A c \in Ballot :
       (c < b) => \E Q \in MCQuorum :
         \A m \in Q : (<<c, v>> \in votes[m] \/ (\A x \in Acceptor : <<c, v>> \notin votes[x] /\ threshold[x] >= c))
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

VoteStep == \E a \in Acceptor, b \in Ballot, v \in Value : Consensus(a, b, v)

Next == \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b) \/ VoteStep

Spec == Init /\ [][Next]_<<votes, threshold>>

\* A vote is only cast if the value is safe at that ballot, meaning every
\* lower ballot is already quorally backed for it or locked out.
Safe ==
  \A a \in Acceptor : \A e \in votes[a] :
    \A c \in Ballot :
      (c < e[1]) => \E Q \in MCQuorum :
        \A m \in Q : (<<c, e[2]>> \in votes[m] \/ (\A x \in Acceptor : <<c, e[2]>> \notin votes[x] /\ threshold[x] >= c))

AtMostOnePerBallot ==
  \A a, b \in Acceptor : \A e, f \in (votes[a] \cap votes[b]) :
    (e[1] = f[1]) => (e[2] = f[2])

\* The chosen set is derived from the votes, so its cardinality stays bounded
\* by the number of values, and the safe invariant forces it to 0 or 1.
Inv == Safe /\ AtMostOnePerBallot /\ TypeOK

Chosen == (Cardinality(VALUE << votes[a1] \cup votes[a2] \cup votes[a3] >>) - 1)
          \div Cardinality(VALUE << votes[a1] \cup votes[a2] \cup votes[a3] >>)
          \in 0..1

\* Refines abstract consensus to the concrete voting mechanism.
ConsensusSpecBar == Chosen = (Cardinality(VALUE << votes[a1] \cup votes[a2] \cup votes[a3] >>) - 1)

====