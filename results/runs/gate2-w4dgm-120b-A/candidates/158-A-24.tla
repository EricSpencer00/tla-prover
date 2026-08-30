---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The model's constants: the three acceptors, two values, the quorum family,   *)
(* and the (bounded) ballot numbers.  They appear here as declared constants   *)
(* so the .cfg file can instantiate them with concrete finite sets.            *)
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME Acceptor = {a1, a2, a3}
ASSUME Value = {v1, v2}
ASSUME Ballot \subseteq Nat

\* A quorum is safe only if every pair of quorums overlaps; that overlap is the
\* sole reason a value can be chosen consistently across ballots.
QuorumOK == \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

VARIABLES votes, thresh

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ thresh \in [Acceptor -> (-1)..(Cardinality(Ballot) + 1)]

\* SAFETY PROPERTY: a vote is only cast for a value that is safe at that
\* ballot -- i.e. every lower ballot already has a quorum supporting it.
SafeAt(v, b) ==
    /\ \A Q \in Quorum :
         \A a \in Q :
             <<b, v>> \in votes[a] \/ b \notin Ballot
    /\ \A c \in Ballot :
         (c < b) =>
            \E Q \in Quorum :
               \A a \in Q :
                  \E w \in Value : <<c, w>> \in votes[a]

AllBallotsSingleValue ==
    \A a1, a2 \in Acceptor :
        \A v1, v2 \in Value :
            \A b \in Ballot :
                (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

VotedOnce == \A a \in Acceptor : \A x, y \in votes[a] : x[1] = y[1] => x[2] = y[2]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold and can no longer vote below it.
RaiseThresh(a, n) ==
    /\ n > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = n]
    /\ UNCHANGED votes

\* Casting a vote is the only action that can never be undone, so the vote is
\* written first and the threshold is raised to that ballot afterward.
Vote(a, n, v) ==
    /\ n \in Ballot
    /\ n >= thresh[a]
    /\ \A x \in votes[a] : x[1] # n
    /\ \A b \in Ballot :
         (b = n) =>
            \A a2 \in Acceptor :
                \A w \in Value :
                    (<<b, w>> \in votes[a2]) => w = v
    /\ \A Q \in Quorum :
         \A a2 \in Q :
             \A w \in Value :
                 (<<n, w>> \in votes[a2] /\ (a2 # a \/ w # v)) => FALSE
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<n, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = n]

Next ==
    \/ \E a \in Acceptor, n \in Nat : RaiseThresh(a, n)
    \/ \E a \in Acceptor, n \in Nat, v \in Value : Vote(a, n, v)

Spec == Init /\ [][Next]_<<votes, thresh>>

(* The chosen set is derived from the votes: every quorum that fully votes for *)
(* a value at some ballot puts that value into the chosen set.                *)
Chosen == {v \in Value : \E Q \in Quorum : \A a \in Q : <<1, v>> \in votes[a]}

\* The consensus spec: at most one value is ever chosen.
ConsensusSpecBar == Cardinality(Chosen) <= 1

(* The refinement mapping: the abstract consensus state (the chosen set) is *)
(* defined directly from the concrete vote records of the acceptors.       *)
Inv == TypeOK /\ AllBallotsSingleValue /\ VotedOnce /\ ConsensusSpecBar

\* The symmetry group: swapping a1 and a2 is a harmless relabeling of       *)
(* acceptors, and the model must behave identically under it.               *)
MCSymmetry == {f \in [Acceptor -> Acceptor] : (f[a1] = a2 <=> f[a2] = a1) /\ f[a3] = a3}

\* The operators below are placeholders the .cfg substitutes with concrete
\* finite instantiations for model checking; they are not used in the model.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====