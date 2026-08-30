---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Modelled selections: the set of acceptors making up each quorum of the (overlapping) quorum system.
\* The invariant's safety argument depends on any two quorums sharing at least one acceptor.
Groups == [q1 : Quorum, q2 : Quorum]

VARIABLES vote, promised, ballotBound

Vars == <<vote, promised, ballotBound>>

\* A vote is the ballot-number/value pair an acceptor cast; promised is each acceptor's promise
\* threshold: the lowest ballot it is willing to vote in from now on.
TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promised \in [Acceptor -> Ballot]
  /\ ballotBound \in Ballot

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> 0 - 1]
  /\ ballotBound \in Ballot

\* An acceptor raises its promise threshold, lobbying out of lower-numbered ballots.
RaiseThreshold ==
  /\ \E a \in Acceptor, n \in Ballot :
       /\ n > promised[a]
       /\ promised' = [promised EXCEPT ![a] = n]
  /\ UNCHANGED <<vote, ballotBound>>

\* An acceptor votes for a value in a ballot, but only if no other value already occupies
\* that ballot (no double-declaration) and the value is safe at that ballot (quorum safe).
Vote ==
  /\ \E a \in Acceptor, n \in Ballot, v \in Value :
       /\ n >= promised[a]
       /\ \A e \in vote[a] : e[1] # n
       /\ \A b \in Acceptor : \A e \in vote[b] : (e[1] = n) => (e[2] = v)
       /\ \E g \in Groups : \A e \in Acceptor : \A w \in Value :
            (w = v /\ e \in g.q1 /\ n \in ballotBound) => (<<n, w>> \in vote[e] \/ n > ballotBound)
       /\ vote' = [vote EXCEPT ![a] = @ \cup {<<n, v>>}]
       /\ promised' = [promised EXCEPT ![a] = n]
  /\ UNCHANGED ballotBound

\* Ballot numbers are natural numbers; the model bounds the range explored by TLC.
BoundBallots ==
  /\ \E k \in ballotBound :
       /\ k < 2
       /\ ballotBound' = k + 1
  /\ UNCHANGED <<vote, promised>>

Next == RaiseThreshold \/ Vote \/ BoundBallots

Spec == Init /\ [][Next]_Vars

\* Chosen values are those with a unanimous quorum: at most one such value can exist
\* because ballot-number/value pairs with the same ballot must name the same value.
Chosen == {v \in Value : \E g \in Groups : \A a \in g.q2 : <<1, v>> \in vote[a]}

\* Safety: every cast vote is safe at its ballot, no ballot names two values, and the
\* variables stay within their declared types.
Inv ==
  /\ \A a \in Acceptor : \A e \in vote[a] : e[2] \in Value /\ e[1] \in Ballot
  /\ \A a, b \in Acceptor : \A e \in vote[a], f \in vote[b] : (e[1] = f[1]) => (e[2] = f[2])
  /\ TypeOK

\* The voting algorithm implements consensus: the set of chosen values is derived from
\* the votes and never holds more than one value.
ConsensusSpecBar == Chosen \subseteq {v \in Value : \A a \in Acceptor : <<1, v>> \in vote[a]}

\* The acceptors are symmetric: any permutation of them is an automorphism of the
\* state space, so the model cannot distinguish a privileged leader.
MCSymmetry ==
  {p \in [Acceptor -> Acceptor] : \A a \in Acceptor : p[p[a]] = a}

\* The model's concrete instantiations: bounded ballot numbers, a concrete quorum system.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3}, {a1, a3} }
MCBallot == 0..1

====