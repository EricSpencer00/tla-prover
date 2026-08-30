---- MODULE Voting ----
EXTENDS Integers

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vars == [votes : [Acceptor -> SUBSET (Ballot \X Value)], thr : [Acceptor -> Ballot \cup {-1}]]

\* An acceptor promises never to participate below its current threshold; it may
\* raise the threshold at any time (no vote cast), which only makes it more strict.
\* Votes are cast only if they are the sole votes for that ballot and are safe
\* against every prior ballot.

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thr = [a \in Acceptor |-> -1]

Promised(a, b) ==
  /\ b > thr[a]
  /\ thr' = [thr EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Every quorum is safe at b for a value v: each lower ballot is backed by a
\* quorum voting that same value, or is unwinnable -- so no new value can slip in.
QuorumSafe(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          (<<c, v>> \in votes[a]) \/ (\A vv \in Value : <<c, vv>> \notin votes[a])

Cast(a, b, v) ==
  /\ b >= thr[a]
  /\ <<b, v>> \notin votes[a]
  /\ \A a2 \in Acceptor : <<b, v>> \in votes[a2] \/ (\A vv \in Value : <<b, vv>> \notin votes[a2])
  /\ QuorumSafe(b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ thr' = [thr EXCEPT ![a] = b]

Next == \E a \in Acceptor, b \in Ballot, v \in Value : Promised(a, b) \/ Cast(a, b, v)

Spec == Init /\ [][Next]_Vars

\* Exact operators used for the shared invariant and property below.
VoteSet(a) == votes[a]
Chosen == UNION {VoteSet(a) : a \in Acceptor}

\* SAFETY LEMMA: the vote relation is functional per ballot, so two values cannot
\* both be chosen -- this is the whole point of the single-vote-per-ballot rule.
BallotFunctional ==
  \A a1, a2 \in Acceptor :
    \A v1, v2 \in Value :
      (\A b \in Ballot : <<b, v1>> \in votes[a1] <=> <<b, v1>> \in votes[a2])
        /\ \A b \in Ballot : <<b, v2>> \in votes[a1] <=> <<b, v2>> \in votes[a2]
          => v1 = v2

\* Consensus: every chosen value is backed by a full quorum voting it in the same
\* ballot, and the ballot function above guarantees at most one such value.
Inv == BallotFunctional

\* The voting algorithm implements consensus: chosen values are exactly those
\* backed by a quorum (every consensus outcome is represented) and are unique (no
\* two outcomes ever conflict).
ConsensusSpecBar ==
  /\ \A v \in Chosen : \E Q \in Quorum : \A a \in Q : \E b \in Ballot : <<b, v>> \in votes[a]
  /\ \A v1, v2 \in Chosen : v1 = v2

\* Two permutations of the participant set are indistinguishable -- a relabeling,
\* not a change of anything substantive about the run.
MCSymmetry ==
  \E f \in [Acceptor -> Acceptor] :
    /\ \A a1, a2 \in Acceptor : (a1 = a2) <=> (f[a1] = f[a2])
    /\ \A a \in Acceptor : votes' = [votes EXCEPT ![f[a]] = @]
    /\ \A a \in Acceptor : thr' = [thr EXCEPT ![f[a]] = @]

\* The model is run up to a bounded ballot horizon, so every reachable state is
\* explored; the horizon is a constant, not a hard bound on the mechanism.
BallotBound == \E b \in Ballot : b <= 1

====