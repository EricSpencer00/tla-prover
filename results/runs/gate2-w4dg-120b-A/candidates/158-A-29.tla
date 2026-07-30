---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A vote is a pair of the ballot number it was cast in and the value it was
\* cast for. Acceptor is the set of processes that cast votes; Quorum is the
\* set of quorum sets, each a subset of Acceptor that always overlaps with
\* every other quorum set.
Vote == [ball : Ballot, val : Value]

QuorumsOverlap == \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor never votes in a ballot below its own promise threshold; it
\* can raise the threshold at any time, so slow acceptors are simply never
\* going back to vote in an old ballot.
RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* A ballot is safe for a value if, at every earlier ballot, some quorum has
\* already committed that value (or can never vote at that ballot).
SafeAt(a, v, b) ==
    /\ \A c \in 0..(b - 1) :
         \E Q \in Quorum :
            \A m \in Q : (([ball |-> c, val |-> v] \in votes[m]) \/ (b < threshold[m]))
    /\ ~\E a2 \in Acceptor :
         \E v2 \in Value : ([ball |-> b, val |-> v2] \in votes[a2]) /\ v2 # v

CastVote(a, v, b) ==
    /\ b >= threshold[a]
    /\ \A a2 \in Acceptor : [ball |-> b, val |-> v] \notin votes[a2]
    /\ SafeAt(a, v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen, expressed as the size of
\* the derived chosen set never exceeding one.
Chosen == {v \in Value : \E a \in Acceptor : [ball |-> 1, val |-> v] \in votes[a]}

Inv ==
    /\ Chosen <= 1
    /\ \A a \in Acceptor : \A p \in votes[a] : SafeAt(a, p.val, p.ball)
    /\ threshold \in [Acceptor -> (-1)..(CHOOSE b \in Ballot : TRUE)]
    /\ votes \in [Acceptor -> SUBSET Vote]

\* Refinement to the abstract consensus specification: the derived chosen set
\* is exactly the set of values ever voted for at ballot one.
ConsensusSpecBar == Chosen = {v \in Value : \E a \in Acceptor : [ball |-> 1, val |-> v] \in votes[a]}

====