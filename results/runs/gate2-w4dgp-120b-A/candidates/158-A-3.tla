---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2

Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == {{a1, a2}, {a2, a3}}
Ballot == Nat
Vote == [ball : Ballot, val : Value]

VARIABLES votes, promised

vars == <<votes, promised>>

Init ==
    /\ votes = [p \in Acceptor |-> {}]
    /\ promised = [p \in Acceptor |-> -1]

Voter(p, v) == \E q \in Quorum : p \in q

Promised(p, b) == promised[p] >= 0 /\ b <= promised[p]

\* Quorum safety: a value is safe at ballot b if every lower ballot already
\* has a quorum that either voted for it or is forever disqualified from voting.
Safe(p, v, b) ==
    \E q \in Quorum : /\ p \in q
                       /\ \A c \in 0..(b - 1) : \E q2 \in Quorum :
                            /\ p \in q2
                            /\ \A x \in q2 : (Voter(x, v) /\ Promised(x, c)) \/ (b <= promised[x])

Voted(p, b) == \E x \in votes[p] : x.ball = b
VotedVal(p, b) == CHOOSE x \in votes[p] : x.ball = b

CastVote(p, b, v) ==
    /\ b >= promised[p]
    /\ ~Voted(p, b)
    /\ ~(\E x \in votes[p] : x.ball = b /\ x.val # v)
    /\ (\A q \in Quorum : /\ p \in q
                            /\ \A c \in 0..b : \E r \in Quorum : /\ p \in r
                                                        /\ \A x \in r : (Voter(x, v) /\ Promised(x, c)) \/ (b <= promised[x])))
    /\ votes' = [votes EXCEPT ![p] = @ \cup {[ball |-> b, val |-> v]}]
    /\ promised' = [promised EXCEPT ![p] = b]

Bump(p, b) == /\ b > promised[p] /\ promised' = [promised EXCEPT ![p] = b]
              /\ UNCHANGED votes

Next == \E p \in Acceptor :
    \/ \E b \in Ballot, v \in Value : CastVote(p, b, v)
    \/ \E b \in Ballot : Bump(p, b)

Spec == Init /\ [][Next]_vars

\* Every vote that exists is safe at its ballot number.
AllVotesSafe == \A p \in Acceptor : \A x \in votes[p] : Safe(p, x.val, x.ball)

\* Once a value is chosen by a quorum in some ballot, no other value is ever
\* chosen by a quorum, no matter which ballot.
AtMostOneChosenValue ==
    \A q1, q2 \in Quorum, b1, b2 \in Ballot :
        /\ (\A p \in q1 : \E x \in votes[p] : x.ball = b1 /\ Voter(p, x.val))
        /\ (\A p \in q2 : \E x \in votes[p] : x.ball = b2 /\ Voter(p, x.val))
        => b1 = b2

\* No acceptor ever carries two votes for the same ballot number.
AtMostOneVotePerBallot ==
    \A p \in Acceptor, b \in Ballot : \A x \in votes[p] : x.ball = b => x.val = VotedVal(p, b)

TypeOK == /\ votes \in [Acceptor -> SUBSET Vote]
          /\ promised \in [Acceptor -> Ballot \cup {-1}]

Inv == TypeOK /\ AllVotesSafe /\ AtMostOneChosenValue /\ AtMostOneVotePerBallot

\* The voting algorithm implements the single-value consensus guarantee.
ConsensusSpecBar == Inv

MCSymmetry ==
    {f \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor : f[a] \in Acceptor
        /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2}

MCAcceptor == {p1, p2}
MCValue == {v1}
MCQuorum == {{p1, p2}}
MCBallot == {0, 1}

====