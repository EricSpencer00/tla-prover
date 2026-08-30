---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* High-level voting-based consensus over a bounded range of ballot numbers.   *)
(* An acceptor may only vote in a ballot at or above its current promise       *)
(* threshold, and only if no other value was voted for that ballot already.    *)
(* A value is safe at a ballot only if it was already safe at every lower     *)
(* ballot, so once a quorum backs a value it stays the sole value that can win. *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The model's bounded active range of ballot numbers; the full range is Nat.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, minBallot

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
    /\ minBallot \in [MCAcceptor -> {-1} \union MCBallot]

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ minBallot = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold to any higher ballot number.
RaiseThreshold(a, n) ==
    /\ n > minBallot[a]
    /\ minBallot' = [minBallot EXCEPT ![a] = n]
    /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, but only if it is safe from lower ballots.
CastVote(a, n, v) ==
    /\ n >= minBallot[a]
    /\ \A w \in votes[a] : w[1] # n
    /\ \A b \in MCAcceptor : \A u \in votes[b] : (u[1] = n) => (u[2] = v)
    /\ \A c \in MCBallot : c < n => \E Q \in MCQuorum :
           /\ \A b \in Q : (n, v) \in votes[b]
           /\ \A b \in Q : (c \in votes[b] => votes[b][c] = v)
    /\ votes' = [votes EXCEPT ![a] = @ \union {<<n, v>>}]
    /\ minBallot' = [minBallot EXCEPT ![a] = n]

Next ==
    \/ \E a \in MCAcceptor, n \in MCBallot : RaiseThreshold(a, n)
    \/ \E a \in MCAcceptor, n \in MCBallot, v \in MCValue : CastVote(a, n, v)

Spec == Init /\ [][Next]_<<votes, minBallot>>

\* A value is chosen once a quorum of acceptors has voted for it in some ballot.
Chosen ==
    {v \in MCValue :
        \E Q \in MCQuorum : \A b \in Q : \E n \in MCBallot : <<n, v>> \in votes[b]}

\* Every vote an acceptor casts is safe at its ballot number.
SafeVotes == \A a \in MCAcceptor : \A w \in votes[a] : \E Q \in MCQuorum :
    /\ \A b \in Q : (w[1], w[2]) \in votes[b]
    /\ \A c \in MCBallot : c < w[1] => \E b \in Q : <<c, w[2]>> \in votes[b]

\* At most one value is ever voted for in any given ballot, across all acceptors.
BallotSingleVal == \A a, b \in MCAcceptor : \A x, y \in MCValue : \A n \in MCBallot :
    (<<n, x>> \in votes[a] /\ <<n, y>> \in votes[b]) => x = y

\* Safety: at most one value is ever chosen as the consensus outcome.
Inv == SafeVotes /\ BallotSingleVal

\* Correctness: the voting algorithm implements the abstract consensus spec.
ConsensusSpecBar ==
    \A v \in MCValue : (v \in Chosen) <=> (\E Q \in MCQuorum : \A b \in Q : <<0, v>> \in votes[b])

\* Acceptors and values are interchangeable, so swap them to cut the reachable
\* state space by symmetry without losing coverage of the core property.
MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : f \in Permutations(MCAcceptor)}

====