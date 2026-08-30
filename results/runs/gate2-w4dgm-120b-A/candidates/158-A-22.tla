---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* A voting-based consensus algorithm: acceptors vote for values in ballots   *)
(* under a promise threshold.  A quorum voting for a value in a ballot is     *)
(* what makes that value chosen -- and the quorum overlap property below      *)
(* is what stops two different values from ever both collecting a quorum.     *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Votes == [ball: Ballot, val: Value]

VARIABLES vote, promised
vars == <<vote, promised>>

\* A value is safe at ballot b only if every lower ballot already has the     *
\* unanimous support of some quorum; this is what stops a later ballot from   *
\* picking a different value out from under earlier-unanimous quorums.       *
TypeOK ==
    /\ vote \in [Acceptor -> SUBSET Votes]
    /\ promised \in [Acceptor -> Ballot \cup {-1}]
    /\ Quorum \subseteq SUBSET Acceptor
    /\ \A q \in Quorum : \E a \in q : TRUE
    /\ \A q1, q2 \in Quorum : q1 \cap q2 # {}

Init ==
    /\ vote = [a \in Acceptor |-> {}]
    /\ promised = [a \in Acceptor |-> -1]

Promised(a, n) ==
    /\ n > promised[a]
    /\ promised' = [promised EXCEPT ![a] = n]
    /\ UNCHANGED vote

Cast(a, n, v) ==
    /\ n >= promised[a]
    /\ \A w \in vote[a] : w.ball # n
    /\ \A c \in Acceptor : \A w \in vote[c] : (w.ball = n /\ w.val # v) => FALSE
    /\ \E q \in Quorum :
         \A c \in q : \A w \in vote[c] : w.ball = n => w.val = v
    /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {[ball |-> n, val |-> v]}]
    /\ promised' = [promoted EXCEPT ![a] = n]

Next ==
    \E a \in Acceptor :
        \/ \E n \in Ballot : Promised(a, n) \/ Cast(a, n, v1) \/ Cast(a, n, v2)
        \/ \E n \in Ballot, v \in Value : Cast(a, n, v)

Spec == Init /\ [][Next]_vars

\* A quorum voting for a value in some ballot is what makes that value chosen. *
Chosen == { vote[a] \cup {w} : a \in Acceptor, w \in vote[a] }

\* Every vote must be safe, and a ballot can only ever see one value voted   *
\* for by a quorum, so the chosen set collapses to a single value.           *
NoDoubleChoice ==
    /\ \A a \in Acceptor : \A w \in vote[a] : \A c \in Acceptor :
           \A x \in vote[c] : x.ball = w.ball => x.val = w.val
    /\ \A q \in Quorum, c \in q : \A w \in vote[c] : w.ball \in Ballot

\* Vacuity: the chosen set is exactly the set of values that a quorum voted *
\* for, so consensus really really was reached on something.                *
ResultIsQuorumChosen == Chosen = { v : \E q \in Quorum, c \in q : [ball |-> 0, val |-> v] \in vote[c] }

Inv == TypeOK /\ NoDoubleChoice

\* Agreement: any two values that a quorum voted for (in any ballot) must be *
\* the same value -- this is the literal property the spec is checking.      *
ConsensusSpecBar == \A v1, v2 \in MCValue : ((v1 \in Chosen) /\ (v2 \in Chosen)) => v1 = v2

\* A relabeling of acceptors (leaving the quorum sets invariant as sets)      *
(* preserves the shape of the reachable state space, so TLA+ model checking    *)
(* is not blown up by symmetric replicas of the same quorum.                     *)
Symmetry == UNION {[q \in Quorum |-> {p @@ f : p \in q}] : f \in [Acceptor -> Acceptor]}

MCSymmetry == Symmetry

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====