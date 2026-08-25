---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* concrete finite versions for model checking *)
MCAcceptor == { a1, a2, a3 }
MCValue   == { v1, v2 }
MCQuorum  == { {a1, a2}, {a2, a3}, {a1, a3} }
MCBallot  == 0..2

VARIABLES votes, thresh

(* --------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* --------------------------------------------------------------------- *)
(*  Actions                                                             *)
(* --------------------------------------------------------------------- *)

Promise ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > thresh[a]
        /\ thresh' = [thresh EXCEPT ![a] = b]
        /\ votes' = votes

Vote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= thresh[a]                                          \* respects promise
        /\ ~\E vv \in votes[a] : vv.ballot = b                     \* not voted in b yet
        /\ ( \A a2 \in Acceptor :
                (\E vv \in votes[a2] : vv.ballot = b) =>
                (\E vv \in votes[a2] : vv.ballot = b /\ vv.value = v) )
        /\ SafeAt(v, b)                                            \* safety condition
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b,
                                                          value  |-> v] }]
        /\ thresh' = [thresh EXCEPT ![a] = b]

Next == Promise \/ Vote

Spec == Init /\ [][Next]_<<votes, thresh>>

(* --------------------------------------------------------------------- *)
(*  Safety of a value at a ballot                                         *)
(* --------------------------------------------------------------------- *)

SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vv \in votes[a] :
                        vv.ballot = c /\ vv.value = v )
                    \/ ( thresh[a] > c )

(* --------------------------------------------------------------------- *)
(*  Chosen value definition                                              *)
(* --------------------------------------------------------------------- *)

Chosen(v) ==
    \E Q \in Quorum :
        \A a \in Q :
            \E vv \in votes[a] : vv.value = v

(* --------------------------------------------------------------------- *)
(*  Invariants                                                          *)
(* --------------------------------------------------------------------- *)

TypeCorrect ==
    /\ \A a \in Acceptor : votes[a] \subseteq [ballot : Ballot, value : Value]
    /\ \A a \in Acceptor : thresh[a] \in Ballot \cup {-1}

SafeVotes ==
    \A a \in Acceptor :
        \A vv \in votes[a] :
            SafeAt(vv.value, vv.ballot)

OneValuePerBallot ==
    \A b \in Ballot :
        ( \E v1 \in Value :
              \E a1 \in Acceptor :
                  [ballot |-> b, value |-> v1] \in votes[a1] ) =>
        ( \A v2 \in Value, a2 \in Acceptor :
              ([ballot |-> b, value |-> v2] \in votes[a2]) => v2 = v1 )

Inv == TypeCorrect /\ SafeVotes /\ OneValuePerBallot

(* --------------------------------------------------------------------- *)
(*  Consensus property                                                  *)
(* --------------------------------------------------------------------- *)

ConsensusSpecBar == [] ( \A v1, v2 \in Value :
                           (Chosen(v1) /\ Chosen(v2)) => v1 = v2 )

(* --------------------------------------------------------------------- *)
(*  Symmetry over acceptors                                              *)
(* --------------------------------------------------------------------- *)

MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor : p[a] \in Acceptor
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2 }

====