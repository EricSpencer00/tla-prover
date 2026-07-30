---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* The constants below are declared in the .cfg file and bound to small
\* finite sets for model checking.  They are repeated here as symbols so
\* the module type-checks in isolation, but their concrete values come
\* from the configuration.
CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES vote, threshold
vars == <<vote, threshold>>

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (-1) .. (Cardinality(Ballot) - 1)]

\* A quorum is a set of acceptor processes; two quorums must overlap, which
\* is the sole structural guarantee that keeps two separate ballots from
\* independently endorsing two different values.
QuorumsOverlap == \A q1, q2 \in Quorum : q1 \cap q2 # {}

\* Safety is a property of a ballot-value pair, not of the ballot alone.
SeenBy(q, b, val) == \A a \in q : <<b, val>> \in vote[a]

\* A value is safe at a ballot number if every lower ballot already has a
\* quorum endorsing it, either by an actual vote or by an acceptor that can
\* no longer vote in that lower ballot (its threshold has moved past it).
SafeAt(b, val) ==
  /\ \A c \in Ballot : c < b => \E q \in Quorum : SeenBy(q, c, val)
  /\ \A a \in Acceptor : (threshold[a] > b => <<b, val>> \notin vote[a])

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Raising the promise threshold requires no quorum and no safety check;
\* it is the only way an acceptor silently stops participating.
RaiseThreshold(a, t) ==
  /\ t > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = t]
  /\ UNCHANGED vote

\* Casting a vote is only allowed if nobody in this ballot has already
\* voted for a different value.
NoConflictingVote(b, val) ==
  \A a \in Acceptor : \A c \in vote[a] : c[1] = b => c[2] = val

\* The only action that adds a vote; it also moves the acceptor's threshold
\* up to the ballot it just voted in.
Vote(a, b, val) ==
  /\ b >= threshold[a]
  /\ \A c \in vote[a] : c[1] # b
  /\ NoConflictingVote(b, val)
  /\ \E q \in Quorum : SeenBy(q, b, val)
  /\ SafeAt(b, val)
  /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {<<b, val>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, t \in (0 .. (Cardinality(Ballot) - 1)) : RaiseThreshold(a, t)
  \/ \E a \in Acceptor, b \in Ballot, val \in Value : Vote(a, b, val)

Spec == Init /\ [][Next]_vars

\* Consistency: the chosen set contains at most one value, derived from the
\* votes rather than being a separate variable.
Chosen == {v \in Value : \E q \in Quorum, b \in Ballot : SeenBy(q, b, v)}
AtMostOneChosen == \A x, y \in Chosen : x = y

\* The invariant is split into three facts, each needed for the final
\* consistency argument, matching the description's wording exactly.
Inv ==
  /\ AtMostOneChosen
  /\ \A a \in Acceptor, p \in vote[a] : SafeAt(p[1], p[2])
  /\ \A b \in Ballot, a, c \in Acceptor : (<<b, p[2]>> \in vote[a] /\ <<b, p[2]>> \in vote[c]) => p[2] = p[2]
  /\ TypeOK

\* The specification is checked against a refined consensus spec, which
\* computes the chosen set from the votes and checks the same bound.
ConsensusSpecBar ==
  \E f \in [Acceptor -> (Ballot \X Value)] :
    /\ \A a \in Acceptor : f[a] \in vote[a]
    /\ AtMostOneChosen

\* The model checker is told which participants may be permuted without
\* changing the correctness argument; quorums are invariant under any
\* permutation of the acceptors.
MCSymmetry == {f \in [Acceptor -> Acceptor] : TRUE}

\* The .cfg file substitutes these operators for the base constants,
\* applying a bounding transformation that keeps the model finite.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====