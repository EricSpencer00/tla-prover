---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* -------------------------------------------------------------------------
   Operators that substitute the constants for model checking
   ------------------------------------------------------------------------- *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(* -------------------------------------------------------------------------
   State variables
   ------------------------------------------------------------------------- *)
VARIABLES votes, thresh

vars == <<votes, thresh>>

(* -------------------------------------------------------------------------
   Type invariants
   ------------------------------------------------------------------------- *)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ thresh \in [Acceptor -> (Ballot \cup {-1})]

(* -------------------------------------------------------------------------
   Safety predicate for a value at a ballot
   ------------------------------------------------------------------------- *)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (thresh[a] > c)

(* -------------------------------------------------------------------------
   At most one value per ballot across all acceptors
   ------------------------------------------------------------------------- *)
OneValuePerBallot ==
    \A b \in Ballot :
        \A a1 \in Acceptor :
            \A v1_ \in Value :
                (<<b, v1_>> \in votes[a1]) =>
                    \A a2 \in Acceptor :
                        \A v2_ \in Value :
                            (<<b, v2_>> \in votes[a2]) => v2_ = v1_

(* -------------------------------------------------------------------------
   Definition of a chosen value (a quorum fully voted for it in some ballot)
   ------------------------------------------------------------------------- *)
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q : <<b, v>> \in votes[a]

(* -------------------------------------------------------------------------
   Invariant required by the .cfg file
   ------------------------------------------------------------------------- *)
Inv ==
    /\ TypeOK
    /\ OneValuePerBallot
    /\ \A a \in Acceptor :
        \A p \in votes[a] :
            Safe(p[2], p[1])

(* -------------------------------------------------------------------------
   Actions
   ------------------------------------------------------------------------- *)

(* Promise: an acceptor raises its threshold *)
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]
    /\ votes' = votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

(* Vote: an acceptor votes for a value in a ballot *)
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]
    /\ ~ (<<b, v>> \in votes[a])                     \* not already voted in this ballot
    /\ \A a2 \in Acceptor :
          \A v2 \in Value :
              (<<b, v2>> \in votes[a2]) => v2 = v   \* at most one value per ballot
    /\ Safe(v, b)                                   \* the value is safe at this ballot
    /\ \E Q \in Quorum :
          \A a2 \in Q :
              (<<b, v>> \in votes[a2]) \/ (thresh[a2] > b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

(* -------------------------------------------------------------------------
   Initialization
   ------------------------------------------------------------------------- *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* -------------------------------------------------------------------------
   Specification
   ------------------------------------------------------------------------- *)
Spec == Init /\ [] [][Next]_vars

(* -------------------------------------------------------------------------
   Liveness / safety property required by the .cfg file
   ------------------------------------------------------------------------- *)
ConsensusSpecBar ==
    [] ( \A v1 \in Value, v2 \in Value :
            (Chosen(v1) /\ Chosen(v2)) => v1 = v2 )

(* -------------------------------------------------------------------------
   Symmetry set (identity permutation)
   ------------------------------------------------------------------------- *)
Id == [a \in Acceptor |-> a]
MCSymmetry == { Id }

=============================================================================