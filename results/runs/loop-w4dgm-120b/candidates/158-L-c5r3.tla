---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

NONE == "none"

VARIABLES votes, threshold

vars == <<votes, threshold>>

VotersFor(v, b) == {a \in Acceptor : <<b, v>> \in votes[a]}
HasAnyVote(b) == \E x \in Acceptor : \E v \in Value : <<b, v>> \in votes[x]

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> (Ballot \cup {NONE})]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> NONE]

\* An acceptor may raise its promise threshold to any higher ballot number; it
\* may then only vote in ballot numbers at or above that threshold.
RaiseThreshold(a, b) ==
    /\ (threshold[a] = NONE \/ b > threshold[a])
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* A quorum of acceptors (guaranteed to overlap with any other quorum) is
\* demonstrated as backing the value's safety at the ballot below.
CastVote(a, b, v) ==
    /\ threshold[a] # NONE => b >= threshold[a]
    /\ \A x \in Acceptor : <<b, v>> \notin votes[x]
    /\ \A x \in Acceptor : (\E c \in Ballot, w \in Value : <<c, w>> \in votes[x]) => c <= b
    /\ \A q \in Quorum : \A c \in Ballot : c < b => \E a2 \in q : <<c, v>> \in votes[a2]
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever carried by a quorum in any ballot.
AtMostOneChosen ==
    /\ \A a1 \in Acceptor, a2 \in Acceptor, b \in Ballot : (votes[a1] \cup votes[a2]) \cap ({b} \X Value) \subseteq {<<b, CHOOSE v \in Value : <<b, v>> \in (votes[a1] \cup votes[a2])>>}
    /\ \A a \in Acceptor, b1 \in Ballot, b2 \in Ballot : (votes[a] \cap ({b1} \X Value)) # {} /\ (votes[a] \cap ({b2} \X Value)) # {} => b1 = b2
    /\ TypeOK

Inv == AtMostOneChosen

\* The chosen value is derived from the votes: a value is in the chosen set iff
\* some quorum has fully voted for it in some ballot.
ChosenFromVotes ==
    \A v \in Value :
        (\E b \in Ballot : HasAnyVote(b) /\ (\E q \in Quorum : \A a \in q : <<b, v>> \in votes[a]))
            <=> HasAnyVote(b)

ConsensusSpecBar == ChosenFromVotes

\* Symmetry: swapping the acceptor identities leaves the reachable states
\* unchanged, so the model checking can factor out that symmetry.
MCSymmetry ==
    {p \in [Acceptor -> Acceptor] : \A a1 \in Acceptor : \E a2 \in Acceptor : p[a2] = a1}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====