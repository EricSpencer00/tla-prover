---- MODULE Voting ----
EXTENDS Naturals, FiniteSets
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot
CONSTANTS MCAcceptor, MCValue, MCQuorum, MCBallot
VARIABLES vote, promised
vars == <<vote, promised>>


None == "none"
Voters == [a \in Acceptor |-> [ballot : Ballot, val : Value]]
Quorums == Quorum
Ballots == Ballot

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET Voters]
  /\ promised \in [Acceptor -> Ballot \cup {None}]
  /\ Acceptor = MCAcceptor
  /\ Value = MCValue
  /\ Quorum = MCQuorum
  /\ Ballot = MCBallot

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> None]

NoVoteInBallot(a, b) ==
  \A w \in vote[a] : w.ballot # b

QuorumMember(a) == \E Q \in Quorums : a \in Q

VoteExists(b, val) ==
  \E Q \in Quorums :
    /\ \A a \in Q : \E w \in vote[a] : w.ballot = b /\ w.val = val
    /\ \A a \in Q, w \in vote[a] : w.ballot = b => w.val = val

QuorumExists(b, val) ==
  \E Q \in Quorums :
    /\ \A a \in Q : \E w \in vote[a] : w.ballot = b /\ w.val = val
    /\ \A a \in Q, w \in vote[a] : w.ballot = b => w.val = val

SafeAtBallot(a, b, val) ==
  /\ VoteExists(b, val)
  /\ \A c \in Ballot : c < b => QuorumExists(c, val)

Promised(a, b) == promised[a] = None \/ b >= promised[a]

Vote(a, b, val) ==
  /\ \E Q \in Quorums :
       /\ \A a2 \in Q : a2 = a
       /\ QuorumMember(a)
  /\ Promised(a, b)
  /\ NoVoteInBallot(a, b)
  /\ SafeAtBallot(a, b, val)
  /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {[ballot |-> b, val |-> val]}]
  /\ promised' = [promised EXCEPT ![a] = b]

Raise(a, b) ==
  /\ Promised(a, b)
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED vote

Next ==
  \/ \E a \in Acceptor, b \in Ballots, val \in Value : Vote(a, b, val)
  \/ \E a \in Acceptor, b \in Ballots : Raise(a, b)

Spec == Init /\ [][Next]_vars

Chosen == {val \in Value : \E Q \in Quorums : \A a \in Q : \E w \in vote[a] : w.val = val}
AtMostOneChosen == \A x \in Chosen, y \in Chosen : x = y

AtMostOneVotedPerBallot ==
  \A a1, a2 \in Acceptor, b \in Ballots :
    (\E w1 \in vote[a1] : w1.ballot = b) /\ (\E w2 \in vote[a2] : w2.ballot = b) => a1 = a2

Inv == TypeOK /\ AtMostOneChosen /\ AtMostOneVotedPerBallot
ConsensusSpecBar == AtMostOneChosen

Symmetric ==
  \E f \in [Acceptor -> Acceptor] :
    /\ \A x \in Acceptor : f[x] \in Acceptor
    /\ \A x \in Acceptor : \A y \in Acceptor :
         /\ x \in f[y] => y \in f[x]
         /\ (x = y <=> f[x] = f[y])
    /\ \A x \in Acceptor : \A y \in Acceptor : f[x] = y => y \in Acceptor
    /\ \A x \in Acceptor : \A y \in Acceptor : f[x] = y => x \in Acceptor

MCSymmetry == {f \in [Acceptor -> Acceptor] : TRUE}
====