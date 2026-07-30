---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* An acceptor can only vote in a ballot number that is at least its promise
\* threshold. It may raise the threshold at any time, which is what makes it
\* refuse to vote in a stale ballot.
\* A ballot is safe for a value iff every lower ballot already has a quorum
\* voting for that value (or is inaccessible). Every vote cast must be safe
\* at its ballot number.
\* The overlap of all quorums is what forces the single-value guarantee.

VARIABLES vote, threshold

vars == <<vote, threshold>>

P(f, a) == [ball |-> a.ball, val |-> f]

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (Ballot \cup {-1})]

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Independent bump of the promise threshold; never drops the threshold.
\* Raising it forbids voting in earlier ballots from this point on.
RaiseThresh(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

HasVotedIn(a, b) ==
  \E v \in Value : <<b, v>> \in vote[a]

\* The ballot is safe for f if every lower ballot already has a quorum solidly
\* behind f. A quorum may be partially cast -- the others simply cannot vote.
\* The ballot numbers are bounded, so this downward chain is finite.
BallotIsSafe(b, f) ==
  \A c \in {x \in Ballot : x < b} :
    \E q \in Quorum :
      \A a \in q : (\E m \in vote[a] : m = P(f, c)) \/ (c < threshold[a])

\* The irreversible step: a vote is only cast if every lower ballot is safe
\* for the same value, so a different value cannot later appear behind a
\* quorum. The ballot is also never cut short by the threshold.
CastVote(a, b, f) ==
  /\ b >= threshold[a]
  /\ ~HasVotedIn(a, b)
  /\ \A a2 \in Acceptor :
        \A f2 \in Value :
          (<<b, f2>> \in vote[a2]) => (f2 = f)
  /\ BallotIsSafe(b, f)
  /\ vote' = [vote EXCEPT ![a] = @ \cup {<<b, f>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThresh(a, b)
  \/ \E a \in Acceptor, b \in Ballot, f \in Value : CastVote(a, b, f)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in Acceptor : \A m \in vote[a] : BallotIsSafe(m.ball, m.val)
  /\ \A a, a2 \in Acceptor : \A b \in Ballot :
        (<<b, Value>> \in vote[a] /\ <<b, Value>> \in vote[a2]) => (a = a2)
  /\ TypeOK

\* A value is chosen once some quorum has solidly committed to it.
Chosen ==
  {f \in Value :
    \E b \in Ballot :
      \E q \in Quorum : \A a \in q : <<b, f>> \in vote[a]}

\* The chosen set never holds two different values; that is the whole point
\* of the safety proof behind BallotIsSafe and the quorum overlap.
ConsensusSpecBar == Cardinality(Chosen) <= 1

====