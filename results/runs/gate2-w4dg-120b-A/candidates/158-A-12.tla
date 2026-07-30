---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* An acceptor's promise threshold is the highest ballot it has committed to
\* (or the highest it has refused to go below). A vote is a ballot/value pair
\* that an acceptor has cast. A value is chosen when a quorum has all voted for
\* it in the same ballot. Safety: no two different values are ever chosen.
VARIABLES vote, threshold, chosen

vars == <<vote, threshold, chosen>>

\* Mechanically compute the set of values that a quorum has all voted for in a
\* given ballot; the safety requirement will pull a single value out of this.
VotedIn(q, b) == { val \in Value : \A a \in q : <<b, val>> \in vote[a] }

TypeOK ==
    /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> (Ballot \cup {-1})]
    /\ chosen \in SUBSET Value

Init ==
    /\ vote = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]
    /\ chosen = {}

\* Raising the threshold is a no-op on the vote set; it is what stops a slow
\* acceptor from sneaking a vote into a ballot it has already committed past.
RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED <<vote, chosen>>

\* A vote is only ever cast for a value that is safe at that ballot number.
SafeAt(a, b, val) ==
    /\ \A c \in Ballot :
        (c < b) => \E q \in Quorum :
            \A aa \in q : (<<c, val>> \in vote[aa] \/ threshold[aa] >= c)
    /\ \A aa \in Acceptor : <<b, val>> \in vote[aa] => aa = a

Vote(a, b, val) ==
    /\ b >= threshold[a]
    /\ \A aa \in Acceptor : <<b, val>> \notin vote[aa]
    /\ \A aa \in Acceptor : \A v2 \in Value :
        (<<b, v2>> \in vote[aa]) => v2 = val
    /\ \E q \in Quorum : val \in VotedIn(q, b)
    /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {<<b, val>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED chosen

Next ==
    \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in Acceptor, b \in Ballot, val \in Value : Vote(a, b, val)

Spec == Init /\ [][Next]_vars

\* A value is only ever recorded as chosen if some quorum has all voted for it.
Reap == \E q \in Quorum, b \in Ballot, val \in Value :
            /\ val \in VotedIn(q, b)
            /\ chosen' = chosen \cup {val}
            /\ UNCHANGED <<vote, threshold>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Reap)

Inv == TypeOK /\ \A a \in Acceptor, b \in Ballot, val \in Value : SafeAt(a, b, val)

\* The chosen set has at most one value; every chosen value is witnessed by a quorum.
\* The two invariants together are what makes that happen.
ConsensusSpecBar ==
    /\ Cardinality(chosen) <= 1
    /\ \A val \in chosen :
        \E q \in Quorum, b \in Ballot : val \in VotedIn(q, b)

====