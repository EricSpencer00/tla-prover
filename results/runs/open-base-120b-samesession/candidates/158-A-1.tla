---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*--- MC operators (substituted constants) ---------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*--- State variables -------------------------------------------------------
VARIABLES votes, prom

\*--- Initial state ---------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

\*--- Safety of a (value,ballot) pair --------------------------------------
Safe(v, b) ==
    /\ b \in Ballot
    /\ \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( [ballot |-> c, value |-> v] \in votes[a] ) \/
                    ( prom[a] > c )

\*--- Helper: the (unique) value that has been voted for in ballot b ------
BallotValue(b) ==
    CHOOSE v \in Value :
        \E a \in Acceptor : \E rec \in votes[a] :
            rec.ballot = b /\ rec.value = v

\*--- Actions ---------------------------------------------------------------
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= prom[a]
    /\ \A rec \in votes[a] : rec.ballot # b
    /\ \A a2 \in Acceptor :
          ( \E rec \in votes[a2] : rec.ballot = b )
          => \E rec \in votes[a2] :
                rec.ballot = b /\ rec.value = v
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ prom'  = [prom  EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor : \E b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Vote(a, b, v)

\*--- Specification ---------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\*--- Invariant ------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor : \A rec \in votes[a] : Safe(rec.value, rec.ballot)
    /\ \A b \in Ballot :
          ( \E a \in Acceptor : \E rec \in votes[a] : rec.ballot = b )
          => \A a' \in Acceptor : \A rec' \in votes[a'] :
                rec'.ballot = b => rec'.value = BallotValue(b)
    /\ \A a \in Acceptor : prom[a] \in Int

\*--- Consensus property (at most one chosen value) -------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        ( (\E q1 \in Quorum : \A a \in q1 :
                \E rec \in votes[a] : rec.value = v1)
          /\ (\E q2 \in Quorum : \A a \in q2 :
                \E rec \in votes[a] : rec.value = v2) )
        => v1 = v2

\*--- Symmetry: permutations of acceptors preserving quorum structure --------
IsBijective(f) ==
    /\ DOMAIN f = Acceptor
    /\ RANGE  f = Acceptor
    /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2

MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        /\ IsBijective(f)
        /\ \A q \in Quorum : Image(f, q) \in Quorum }

====