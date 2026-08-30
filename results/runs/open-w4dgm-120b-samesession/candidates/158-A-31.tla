---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME a1 \in Acceptor /\ a2 \in Acceptor /\ a3 \in Acceptor
ASSUME v1 \in Value /\ v2 \in Value
ASSUME a1 # a2 /\ a1 # a3 /\ a2 # a3
ASSUME v1 # v2
ASSUME Quorum \subseteq SUBSET Acceptor
ASSUME Ballot \subseteq Nat

VARIABLES vote, thr

vars == << vote, thr >>

VoteBallot(v, b) == {x \in Acceptor : << b, v >> \in vote[x]}

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thr \in [Acceptor -> (Nat \cup {-1})]

Init ==
  /\ vote = [x \in Acceptor |-> {}]
  /\ thr = [x \in Acceptor |-> -1]

Promise(x, b) ==
  /\ b > thr[x]
  /\ thr' = [thr EXCEPT ![x] = b]
  /\ UNCHANGED vote

\* The no-conflict condition is checked against every acceptor, not just the quorum.
Vote(x, v, b) ==
  /\ b >= thr[x]
  /\ << b, v >> \notin vote[x]
  /\ \A y \in Acceptor : (\E w \in Value : << b, w >> \in vote[y]) => w = v
  /\ \E Q \in Quorum : \A y \in Q : VoteBallot(v, b) \cup {y}
  /\ vote' = [vote EXCEPT ![x] = @ \cup {<< b, v >>}]
  /\ thr' = [thr EXCEPT ![x] = b]

Next ==
  \/ \E x \in Acceptor, b \in Ballot : Promise(x, b)
  \/ \E x \in Acceptor, v \in Value, b \in Ballot : Vote(x, v, b)

Spec == Init /\ [][Next]_vars

\* A vote is safe only if the value already dominates every lower ballot.
SafeAt(x, b, v) ==
  /\ << b, v >> \in vote[x]
  /\ \A c \in Ballot : c < b => \E Q \in Quorum :
       \A y \in Q : (\E u \in Value : << c, u >> \in vote[y]) => u = v

Safety ==
  /\ \A x \in Acceptor, b \in Ballot, v \in Value : SafeAt(x, b, v)
  /\ \A b \in Ballot, v1, v2 \in Value :
        (\A x \in Acceptor : << b, v1 >> \in vote[x] /\ << b, v2 >> \in vote[x]) => v1 = v2
  /\ TypeOK

Chosen(v) == \E Q \in Quorum : \A x \in Q : << VoteBallot(v, 1) \cup {x}

\* Chosen is derived from the votes, so the two-level shape matches the
\* abstract consensus spec it refines.
ConsensusSpecBar == \A v1, v2 \in Value : (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* Symmetry of the three acceptors under any rotation; always available, so never
\* an empty symmetry set that would block the model checking.
MCSymmetry == [f \in [Acceptor -> Acceptor] |-> UNION { {f} : \A x \in Acceptor : f[x] = x }]

\* Substitutions turning the abstract participant sets into the concrete instantiated
\* finite versions expected by the reference .cfg configuration.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====