---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q1, q2}
MCBallot == {0, 1}

\* The actions below refer to the generic names (Acceptor, Value, Quorum, Ballot);
\* they are instantiated to the finite versions by the .cfg's substitution section.

VARIABLES votes, threshold

vars == <<votes, threshold>>

VotePairs == [ball : Ballot, val : Value]
Votes == [who : Acceptor, pair : VotePairs]

Init ==
    /\ votes = {}
    /\ threshold = [a \in Acceptor |-> -1]

\* Raising a promise only marks off the ballot numbers a process will no
\* longer participate in; it does not commit a value.
Promise(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* The quorum requirement is written as an existential over the supplied
\* collection of quorums, which is what makes the overlap assumption usable.
CastVote(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A w \in Acceptor : (w, [ball |-> b, val |-> v]) \notin votes
    /\ ~ \E w \in Acceptor, wv \in Value :
            wv # v /\ (w, [ball |-> b, val |-> wv]) \in votes
    /\ \E q \in Quorum :
         \A w \in q :
            \/ (w, [ball |-> b, val |-> v]) \in votes
            \/ \A c \in Ballot : c < b => threshold[w] >= c
    /\ votes' = votes \cup { [who |-> a, pair |-> [ball |-> b, val |-> v]] }
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A chosen value is one that some quorum has unanimously voted for at some
\* ballot; it certifies that the value's support is backed by a majority.
ChosenValues ==
    {v \in Value :
        \E q \in Quorum, b \in Ballot :
            \A a \in q : [who |-> a, pair |-> [ball |-> b, val |-> v]] \in votes}

Inv ==
    /\ votes \subseteq Acceptor \X VotePairs
    /\ \A p \in votes :
         /\ p.who \in Acceptor
         /\ p.pair.val \in Value
         /\ p.pair.ball \in Ballot
         /\ \A w \in Acceptor, c \in Ballot :
              (c < p.pair.ball /\ threshold[w] >= c)
                  => \E q \in Quorum : w \in q
    /\ \A b \in Ballot :
         \A v1, v2 \in Value :
             (\A a \in Acceptor : [a, [b, v1]] \in votes /\ [a, [b, v2]] \in votes)
                 => v1 = v2

ConsensusSpecBar ==
    \A v1, v2 \in ChosenValues : v1 = v2

\* The Quorum constant must be instantiated so every pair of quorums overlaps;
\* the symmetry group is the full set of permutations of the acceptor constants.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A x \in Acceptor : f[x] = x}

====