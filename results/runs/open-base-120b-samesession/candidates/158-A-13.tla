---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* substitution operators for the model checker *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

(*---------------------------------------------------*)
(* Helper definitions                                 *)
(*---------------------------------------------------*)

Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

Increase ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > threshold[a]
        /\ threshold' = [threshold EXCEPT ![a] = b]
        /\ UNCHANGED votes

Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( \E vv \in votes[a] : vv[1] = c /\ vv[2] = v )
                    \/ (threshold[a] > c)

Vote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= threshold[a]
        /\ \A vv \in votes[a] : vv[1] # b       \* a has not voted in ballot b yet
        /\ \A a2 \in Acceptor :
                a2 # a =>
                    \A vv2 \in votes[a2] :
                        ~(vv2[1] = b /\ vv2[2] # v)   \* no different value in same ballot
        /\ \E q \in Quorum :
                \A a2 \in q :
                    ( \E vv \in votes[a2] : vv[1] = b /\ vv[2] = v )
                    \/ (threshold[a2] > b)
        /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
        /\ threshold' = [threshold EXCEPT ![a] = b]
        /\ UNCHANGED << >>

Next ==
    \/ Increase
    \/ Vote

(*---------------------------------------------------*)
(* Invariant definitions                             *)
(*---------------------------------------------------*)

TypeInv ==
    /\ votes    \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> Int]

ThreshInv ==
    \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}

SafetyInv ==
    \A a \in Acceptor :
        \A vv \in votes[a] : Safe(vv[1], vv[2])

UniqueBallotInv ==
    \A b \in Ballot :
        ( \E v \in Value, a \in Acceptor : <<b, v>> \in votes[a] ) =>
        ( \A a2 \in Acceptor, v2 \in Value :
              (<<b, v2>> \in votes[a2]) => v2 = v )

Inv == /\ TypeInv /\ ThreshInv /\ SafetyInv /\ UniqueBallotInv

(*---------------------------------------------------*)
(* Specification                                      *)
(*---------------------------------------------------*)

Spec == Init /\ [][Next]_<<votes, threshold>>

(*---------------------------------------------------*)
(* Derived concepts                                   *)
(*---------------------------------------------------*)

Chosen ==
    { v \in Value :
        \E b \in Ballot, q \in Quorum :
            \A a \in q : <<b, v>> \in votes[a] }

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

(*---------------------------------------------------*)
(* Symmetry definition                                *)
(*---------------------------------------------------*)

MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2   \* injective
        /\ \A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a   \* surjective
    }

(*---------------------------------------------------*)
(* Assumption about quorum overlap (not exported)    *)
(*---------------------------------------------------*)

QuorumOverlap ==
    \A q1 \in Quorum, q2 \in Quorum :
        q1 # q2 => q1 \cap q2 # {}

====