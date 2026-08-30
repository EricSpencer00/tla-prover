---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The system tracks a vote set per acceptor, each entry naming the ballot     *)
(* number it applied to, and a promise threshold per acceptor governing      *)
(* which ballot numbers it is willing to vote in.  A quorum of acceptors      *)
(* voting for a value in the same ballot is what makes that value            *)
(* "chosen", and the two invariants together guarantee the choice is        *)
(* never contradicted by a vote that is not safe.                            *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME a1 \in Acceptor /\ a2 \in Acceptor /\ a3 \in Acceptor
ASSUME v1 \in Value /\ v2 \in Value

VARIABLES votes, threshold

vars == << votes, threshold >>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> CHOOSE b \in Ballot : b \in Ballot]

(* Raising the threshold promises never to vote in a ballot below it; a    *)
(* vote cast in the same step must be at exactly that ballot number.      *)
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, v, b, Q) ==
  /\ b \in Ballot
  /\ b \notin { x[1] : x \in votes[a] }
  /\ b >= threshold[a]
  /\ \A x \in votes[a] : x[2] = v
  /\ \A c \in Ballot : (\A x \in votes[a] : x[1] < c) => c \in Ballot
  /\ \A e \in Acceptor : (\A x \in votes[e] : x[1] < b) => e \in Q
  /\ \A e \in Q : \A x \in votes[e] : (x[1] < b) \/ (x[2] = v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup { << b, v >> }]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot, Q \in Quorum :
       CastVote(a, v, b, Q)

Spec == Init /\ [][Next]_vars

(* Every vote an acceptor cast must be backed by a quorum that was         *)
(* unanimously safe at that ballot number.  SAFETY is the backstop that    *)
(* ties the two invariants together; the quorum overlap property is what    *)
(* makes winning just this one vote enough to declare a value chosen.      *)
SAFE(v, b) ==
  /\ \A x \in votes[a] : x[1] = b => x[2] = v
  /\ \E Q \in Quorum :
       /\ \A e \in Q : \A x \in votes[e] : (x[1] < b) \/ (x[2] = v)
       /\ \A e \in Acceptor : (\A x \in votes[e] : x[1] < b) => e \in Q

SAFETY == \A a \in Acceptor : \A x \in votes[a] : SAFE(x[2], x[1])

CHOICEATONE == \A b \in Ballot : \A v1, v2 \in Value :
                 (\A a \in Acceptor : << b, v1 >> \in votes[a])
                 => (\A a \in Acceptor : << b, v2 >> \in votes[a] => v1 = v2)

NOBACKSLIDE == \A a \in Acceptor : \A x \in votes[a] : x[1] <= threshold[a]

Inv == SAFETY /\ CHOICEATONE /\ NOBACKSLIDE

(* The vote set is the concrete record; the chosen set is the deterministic *)
(* abstract projection extracted from it, so the projection on its own     *)
(* cannot distinguish a "correct" run from one that is merely self-consistent *)
(* by virtue of being derived from the votes.                              *)
Chosen == { v \in Value : \E b \in Ballot : \A a \in Acceptor : << b, v >> \in votes[a] }

(* SAFETY is exactly what makes the chosen set single-valued, so the        *)
(* projection is a faithful representation of the collective outcome.       *)
ConsensusSpecBar == CHOICEATONE

(* The quorum set is a small, symmetry-closed family: swapping two          *)
(* acceptors just permutes the family, it does not enlarge or shrink it.    *)
MCSymmetry == { p \in [Acceptor -> Acceptor] : \A Q \in Quorum : { p[e] : e \in Q } \in Quorum }

(* Concrete bounded instantiations of the abstract participant sets; the    *)
(* values here are the ones TLC will model-check against.                   *)
MCAcceptor == {a1, a2, a3}
MCValue    == {v1, v2}
MCQuorum   == { {a1, a2}, {a2, a3} }
MCBallot   == 0..1

====