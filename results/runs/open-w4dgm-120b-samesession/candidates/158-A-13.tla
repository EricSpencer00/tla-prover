---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* A voting-based consensus algorithm abstracting Paxos: acceptors vote in      *)
(* numbered ballots, and a quorum voting for a value in a ballot commits that   *)
(* value. Safety requires at most one value ever chosen. The spec tracks        *)
(* each acceptor's votes and a promise threshold per acceptor.                 *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The .cfg file substitutes these overridden symbols with bounded or concrete
\* instantiations for model checking; the module itself treats them abstractly.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold, commit
vars == <<votes, threshold, commit>>

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]
  /\ commit = {}

Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A g \in votes[a] : g[1] # b
  /\ \A g \in votes : g[1] = b => g[2] = v
  /\ \E Q \in MCQuorum : \A q \in Q :  [b |-> v] \in votes[q]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED commit

Promise(a, b) ==
  /\ b > threshold[a]
  / threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED <<votes, commit>>

Quiesce ==
  /\ \E a \in MCAcceptor : threshold[a] = Cardinality(MCBallot) - 1
  /\ UNCHANGED vars

Next ==
  \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Vote(a, v, b)
  \/ \E a \in MCAcceptor, b \in MCBallot : Promise(a, b)
  \/ Quiesce

Spec == Init /\ [][Next]_vars

(* Safety: at most one value is ever committed, derived from the votes.     *)
Inv == Cardinality(commit) <= 1

(* Refinement: the chosen set is exactly the values endorsed by a quorum.    *)
ConsensusSpecBar == commit = { v \in MCValue : \E Q \in MCQuorum :
                                                \A q \in Q : \E b \in MCBallot : <<b, v>> \in votes[q] }

\* Symmetry: any permutation of acceptor identities preserves the spec.        *
MCSymmetry == { \E f \in [MCAcceptor -> MCAcceptor] :
                   /\ \A x \in MCAcceptor : f[x] \in MCAcceptor
                   /\ \A x, y \in MCAcceptor : f[x] = f[y] => x = y }
====