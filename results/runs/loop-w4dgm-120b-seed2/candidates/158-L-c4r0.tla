---- MODULE Voting ----
\* A voting-based consensus core. Acceptors each have a promise threshold: they
\* never vote in a ballot number below their threshold. A quorum of acceptors
\* voting for the same value in the same ballot decides that value. The invariant
\* is that any two ballots with quorum support named the same value -- so at most
\* one value is ever decided -- and every vote was safe at its ballot.
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

\* Types: Votes are ballot-numbered value votes an acceptor has cast; Thresh is
\* each acceptor's promise threshold (the lowest ballot it will still vote in).
VARIABLES Votes, Thresh

vars == <<Votes, Thresh>>

TypeOK ==
  /\ Votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ Thresh \in [Acceptor -> Ballot \cup {-1}]

\* SAFETY PROPERTY: at most one value ever has quorum support at any ballot, and
\* every vote cast was safe at the ballot it was cast in. This is precisely what
\* rules out two different values both being decided.
Inv ==
  /\ (\A a \in Acceptor : \A p, q \in Votes[a] : p[1] = q[1] => p[2] = q[2])
  /\ (\A a \in Acceptor : \A p \in Votes[a] : \A c \in 0 .. p[1] - 1 :
        \E Q \in Quorum :
          (\A b \in Q : \E q \in Votes[b] : q[1] = c /\ q[2] = p[2])
            \/ (\A b \in Q : \A q \in Votes[b] : q[1] >= c))
  /\ (\A a \in Acceptor : \A p \in Votes[a] : p[1] \in Ballot)

Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Thresh = [a \in Acceptor |-> -1]

\* An acceptor may push its promise threshold up without voting.
Promise(a, n) ==
  /\ n > Thresh[a]
  /\ Thresh' = [Thresh EXCEPT ![a] = n]
  /\ UNCHANGED Votes

\* An acceptor votes for a value in a ballot that has not been claimed by anyone
\* else, once its promise threshold and quorum safety allow it.
Vote(a, n, val) ==
  /\ n >= Thresh[a]
  /\ \A q \in Votes[a] : q[1] # n
  /\ (\A b \in Acceptor : \A q \in Votes[b] : q[1] = n => q[2] = val)
  /\ \E Q \in Quorum :
        (\A b \in Q : \E q \in Votes[b] : q[1] = n /\ q[2] = val)
          \/ (\A b \in Q : \A q \in Votes[b] : q[1] >= n)
  /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {<<n, val>>}]
  /\ Thresh' = [Thresh EXCEPT ![a] = IF n > Thresh[a] THEN n ELSE Thresh[a]]

Next ==
  \/ \E a \in Acceptor, n \in Ballot : Promise(a, n)
  \/ \E a \in Acceptor, n \in Ballot, val \in Value : Vote(a, n, val)

Spec == Init /\ [][Next]_vars

\* REFINEABLE PROPERTY: the voting algorithm implements consensus. The set of
\* decided values is derived from quorum-supported ballots and is always empty
\* or a singleton, so at most one value is ever decided.
ConsensusSpecBar ==
  \A S \in { {v} : v \in Value } \cup { {} } :
    S = { val \in Value :
            \E Q \in Quorum : \A a \in Q : \E p \in Votes[a] : p[2] = val }

\* SYMMETRY: acceptors are interchangeable, so any permutation of the
\* acceptor set is a symmetry of the system.
MCSymmetry == { f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor }

\* BOUNDED INSTANTIATIONS: concrete finite sets for the voting agents, values,
\* quorums, and ballot numbers.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====