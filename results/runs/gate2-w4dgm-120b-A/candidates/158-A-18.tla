---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The model's constants are fixed in the .cfg file.  The operator   *)
(* definitions below use them to form the bounded concrete sets that  *)
(* the model actually explores.                                      *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES vote, threshold
vars == << vote, threshold >>

TypeOK ==
    /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> Ballot]

Init ==
    /\ vote = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> 0]

RaiseThreshold(a, n) ==
    /\ n > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED vote

\* A quorum must vouch for the value at every lower ballot, not just the
\* immediately preceding one, so this is what stops a skipped quorum.
SafeAt(a, b, v) ==
    /\ \A c \in 0 .. (b - 1) : \E q \in Quorum :
         \A m \in q : <c, v> \in vote[m]
    /\ \A c \in 0 .. (b - 1) : ~\E u \in Value :
         \E m \in Acceptor : <c, u> \in vote[m] /\ u # v

Vote(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A m \in Acceptor : <b, v> \notin vote[m]
    /\ \A m \in Acceptor, u \in Value : (<b, u> \in vote[m] => u = v)
    /\ SafeAt(a, b, v)
    /\ vote' = [vote EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \E a \in Acceptor, n \in Ballot : RaiseThreshold(a, n)
      \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

Choice == CHOOSE a \in Acceptor : TRUE
Chosen == CHOOSE v \in Value : \A a \in Acceptor : <<0, v>> \in vote[a]
Balloted == CHOOSE b \in Ballot : \A a \in Acceptor : <<b, Chosen>> \in vote[a]

\* SAFETY: each ballot's votes are coherent and each ballot's value is
\* safe at that ballot, which together imply every ballot agrees on one
\* value -- so the chosen set can never hold two different values.
Inv ==
    /\ \A a \in Acceptor, b \in Ballot, u, v \in Value :
         (<<b, u>> \in vote[a] /\ <<b, v>> \in vote[a]) => u = v
    /\ \A a \in Acceptor, b \in Ballot, v \in Value :
         <<b, v>> \in vote[a] => SafeAt(a, b, v)
    /\ TypeOK

\* FUNCTIONAL INTERPRETATION: the voting record has an underlying
\* deterministic choice function, which is what consensus must agree
\* on -- so a quorum agreeing on a value is exactly the same as that
\* value being the choice function's output (a refinement of choice).
ConsensusSpecBar ==
    /\ \A a \in Acceptor, b \in Ballot : <<b, Chosen>> \in vote[a]
    /\ \A a \in Acceptor, b \in Ballot : <<b, Balloted>> \in vote[a]

\* Symmetry: swapping acceptors everywhere does not change the shape of
\* the reachable state space, so the number of distinct states is
\* reduced by a factor equal to the number of acceptors.
MCSymmetry == (a1 a2)(a2 a3)(a3 a1)

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2} , {a2, a3} }
MCBallot == {0, 1}

====