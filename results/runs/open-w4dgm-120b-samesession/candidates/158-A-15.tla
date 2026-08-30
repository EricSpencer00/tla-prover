---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Safety via quorum overlap: a quorum voting for a value at a ballot certifies
\* that all lower ballots already held a unanimous quorum for that value.
VARIABLES votes, thresh

\* votes[a] is the set of (ballot, value) votes a has cast.
Vars == <<votes, thresh>>

\* No promise made yet: an acceptor will vote in a ballot no lower than its
\* threshold, so a raised threshold rules out older ballots outright.
Init == /\ votes = [a \in Acceptor |-> {}]
        /\ thresh = [a \in Acceptor |-> -1]

MakePromise(a) == /\ \E b \in Ballot :
                      /\ b >= thresh[a]
                      /\ thresh' = [thresh EXCEPT ![a] = b]
                  /\ UNCHANGED votes

\* Vote for a value in a ballot, but only if the ballot is open to this
\* acceptor, no one else voted differently in it, and a quorum vouches for
\* this value being safe at this ballot (no conflicting vote below it).
CastVote(a) == /\ \E b \in Ballot, v \in Value :
                   /\ b >= thresh[a]
                   /\ \A w \in Value : <<b, w>> \notin votes[a]
                   /\ \A q \in Quorum : \A c \in q :
                         /\ \A w \in Value : <<b, w>> \notin votes[c]
                         /\ \E p \in q : <<b, v>> \in votes[p]
                   /\ \A c \in Acceptor : \A cbal \in Ballot :
                         /\ cbal < b
                         /\ \A w \in Value : <<cbal, w>> \in votes[c]
                         => w = v
                   /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
                   /\ thresh' = [thresh EXCEPT ![a] = b]

Next == \/ \E a \in Acceptor : MakePromise(a)
        \/ \E a \in Acceptor : CastVote(a)

Spec == Init /\ [][Next]_Vars

\* A value is unanimous in a ballot once every acceptor in some quorum voted
\* for it in that ballot; a quorum is also an audit trail for the ballot.
Unanimous(b, v) == \E q \in Quorum : \A a \in q : <<b, v>> \in votes[a]

\* An acceptor's vote is safe at its ballot only if every lower ballot already
\* held a unanimous quorum for the same value.
VoteIsSafe == \A a \in Acceptor : \A v \in Value : \A b \in Ballot :
                 <<b, v>> \in votes[a] =>
                    \A c \in Ballot : c < b => Unanimous(c, v)

\* Safety (at most one chosen value) follows from: votes are safe, ballots are
\* unanimous per value, and votes and thresholds are typed.
Inv == /\ VoteIsSafe
       /\ \A b \in Ballot : \A v, w \in Value :
            (\A a \in Acceptor : <<b, v>> \in votes[a])
              => (\A a \in Acceptor : <<b, w>> \in votes[a]) => v = w
       /\ \A a \in Acceptor : \A p, q \in Ballot \times Value :
            ((p \in votes[a]) # (q \in votes[a])) => (p[1] = q[1] => p[2] = q[2])
       /\ \A a \in Acceptor : thresh[a] \in Ballot \cup {-1}

\* The voting algorithm implements a quorum-consensus specification via this
\* refinement mapping: a value is considered 'chosen' exactly when a quorum of
\* acceptors voted for it at some ballot.
ConsensusSpecBar == \A v \in Value : UnanimousBallot(v)
UnanimousBallot(v) == \E b \in Ballot : Unanimous(b, v)

MCSymmetry == { f \in [Acceptor -> Acceptor] :
                   \A q \in Quorum : f[q] \in Quorum }

\* The .cfg substitutes these definitions for the constants they name:
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====