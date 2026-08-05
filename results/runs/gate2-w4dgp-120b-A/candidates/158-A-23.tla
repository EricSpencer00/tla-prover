---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* Permutations of acceptors; symmetry reduces indistinguishable voting processes.
\* MCAcceptor/MCValue/MCQuorum/MCBallot are the bound-checked instances used by TLC.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* A quorum demonstrates that every member has either already voted for the value in
\* this ballot or can never vote in this ballot again.
QuorumSafe(q, v, b) ==
  /\ \A x \in q : \E c \in votes[x] : c[1] = b /\ c[2] = v
  /\ \A x \in q : \A c \in votes[x] : c[1] >= b => c[2] = v

NoVote(v, b) == \A x \in MCAcceptor : ~\E c \in votes[x] : c[1] = b /\ c[2] # v

\* A value is safe at ballot b if the same value was voted for in every lower
\* ballot that already had a quorum vote; otherwise a later quorum could contradict.
ValueSafe(v, b) ==
  /\ \A c \in 0..(b - 1) : \E q \in MCQuorum : QuorumSafe(q, v, c)
  /\ NoVote(v, b)

Init ==
  /\ votes = [x \in MCAcceptor |-> {}]
  /\ threshold = [x \in MCAcceptor |-> -1]

Promise(x, b) ==
  /\ b > threshold[x]
  /\ threshold' = [threshold EXCEPT ![x] = b]
  /\ UNCHANGED votes

\* An acceptor may vote once in a ballot, for at most one value that is safe and
\* promised at that ballot or higher.
CastVote(x, b, v) ==
  /\ b >= threshold[x]
  /\ \A c \in votes[x] : c[1] # b
  /\ NoVote(v, b)
  /\ \E q \in MCQuorum : QuorumSafe(q, v, b)
  /\ votes' = [votes EXCEPT ![x] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![x] = b]

Next ==
  \/ \E x \in MCAcceptor, b \in MCBallot : Promise(x, b)
  \/ \E x \in MCAcceptor, b \in MCBallot, v \in MCValue : CastVote(x, b, v)

Spec == Init /\ [][Next]_vars

\* Chosen is the set of values that at least one quorum voted for.
Chosen == {v \in MCValue : \E q \in MCQuorum : \E x \in q : <<x, v>> \in votes[x]}

Inv ==
  /\ \A x \in MCAcceptor : \A c \in votes[x] : ValueSafe(c[2], c[1])
  /\ \A b \in MCBallot : \A x1 \in MCAcceptor, x2 \in MCAcceptor, v1 \in MCValue, v2 \in MCValue :
        (<<b, v1>> \in votes[x1] /\ <<b, v2>> \in votes[x2]) => v1 = v2

\* A quorum vote on one value precludes any quorum vote on a different value.
ConsensusSpecBar ==
  \A q1 \in MCQuorum, q2 \in MCQuorum, v1 \in MCValue, v2 \in MCValue :
    (\A x \in q1 : <<x, v1>> \in votes[x] /\ \A y \in q2 : <<y, v2>> \in votes[y]) => v1 = v2

\* Permutation symmetry: swapping the identities of two acceptors leaves the
\* reachable states and the chosen set unchanged.
MCSymmetry ==
  { s \in [x \in MCAcceptor |-> [votes : SUBSET (MCBallot \X MCValue), threshold : Nat]]
      : \E p \in (MCAcceptor -> MCAcceptor) :
          (\A x \in MCAcceptor : s[x].votes = votes[p[x]]
           /\ \A x \in MCAcceptor : s[x].threshold = threshold[p[x]]) }

====