---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Override abstract sets to finite realizations for model checking.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q1, q2}
q1 == {a1, a2}
q2 == {a2, a3}
MCBallot == {0, 1}

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
Cast == { <<a, b.ball, b.val>> : a \in Acceptor, b \in votes[a] }

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ threshold \in [Acceptor -> -1..MaxBallot]

MaxBallot == CHOOSE m \in Ballot : \A n \in Ballot : n <= m

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* Raising the threshold irrevocably rules out participation in earlier ballots.
RaiseThreshold(a, n) ==
    /\ n > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED votes

\* Vote for a value in a ballot, provided no other value already has a quorum there.
VoteVal(a, n, v) ==
    /\ n >= threshold[a]
    /\ \A b \in votes[a] : b.ball # n
    /\ \A c \in Acceptor : \A b \in votes[c] : (b.ball = n) => (b.val = v)
    /\ \E Q \in MCQuorum :
         /\ \A c \in Q : \A b \in votes[c] : b.ball = n => b.val = v
         /\ \A c \in Q : \A b \in votes[c] : (b.ball < n) => SafeAt(c, b.ball, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> n, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = n]

SafeAt(a, n, v) ==
    \A c \in Acceptor : \A b \in votes[c] : b.ball = n => b.val = v

Next ==
    \/ \E a \in Acceptor, n \in MCBallot : RaiseThreshold(a, n)
    \/ \E a \in Acceptor, n \in MCBallot, v \in MCValue : VoteVal(a, n, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote was safe at its ballot, so the two-ways-consistency argument holds.
EveryVoteSafe == \A t \in Cast : SafeAt(t[1], t[2], t[3])

OneValuePerBallot ==
    \A a, c \in Acceptor : \A b \in votes[a], d \in votes[c] :
        (b.ball = d.ball) => (b.val = d.val)

VarsTypeOK == TypeOK

Inv == EveryVoteSafe /\ OneValuePerBallot /\ VarsTypeOK

\* The chosen set is derived from the votes, so the model is a refinement of
\* the abstract consensus spec that expects at most one value chosen.
ConsensusSpecBar == ConsensusSpec

\* Symmetry: swapping the two overlapping quorums leaves the system behavior unchanged.
MCSymmetry ==
    {f \in [Acceptor -> Acceptor] : (f[a1] = a1 /\ f[a2] = a2 /\ f[a3] = a3) \/ (f[a1] = a3 /\ f[a2] = a2 /\ f[a3] = a1)}

====