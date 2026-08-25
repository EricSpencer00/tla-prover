---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    a1, a2, a3,
    v1, v2,
    Acceptor, Value, Quorum, Ballot

(* ---------------------------------------------------------------------- *)
(*  Operators that will be substituted by the model checker configuration  *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(* ---------------------------------------------------------------------- *)
VARIABLES Votes, Threshold

(* ---------------------------------------------------------------------- *)
(*  Types of the variables                                                *)
TypeInvariant ==
    /\ Votes    \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    /\ Threshold \in [Acceptor -> Int]

(* ---------------------------------------------------------------------- *)
(*  Safety of a value at a ballot number                                  *)
Safe(v, b) ==
    \A c \in Ballot :
        c < b =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vv \in Votes[a] :
                        /\ vv.ballot = c
                        /\ vv.value  = v )
                    \/ Threshold[a] > c

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                         *)
Init ==
    /\ Votes    = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

(* ---------------------------------------------------------------------- *)
(*  Action: an acceptor raises its promise threshold                      *)
PromiseIncrease ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > Threshold[a]
        /\ UNCHANGED Votes
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

(* ---------------------------------------------------------------------- *)
(*  Action: an acceptor casts a vote                                      *)
Vote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= Threshold[a]                                   \* not below current threshold
        /\ \A vv \in Votes[a] : vv.ballot # b                  \* hasn't voted in this ballot
        /\ \A a2 \in Acceptor :
               ( \E vv2 \in Votes[a2] : vv2.ballot = b )
               => ( \A vv2 \in Votes[a2] :
                       vv2.ballot = b => vv2.value = v )    \* no different value in same ballot
        /\ Safe(v, b)                                          \* a quorum shows the value is safe
        /\ Votes'    = [Votes EXCEPT ![a] = Votes[a] \cup 
                           { [ballot |-> b, value |-> v] } ]
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

(* ---------------------------------------------------------------------- *)
Next ==
    \/ PromiseIncrease
    \/ Vote

Spec ==
    Init /\ [][Next]_<<Votes, Threshold>>

(* ---------------------------------------------------------------------- *)
(*  Invariant: type correctness, safety of every vote, at most one value per ballot,
    and quorum overlap property                                           *)
Inv ==
    /\ TypeInvariant
    /\ \A a \in Acceptor :
          \A vv \in Votes[a] : Safe(vv.value, vv.ballot)
    /\ \A b \in Ballot :
          ( \E v \in Value, a \in Acceptor, vv \in Votes[a] :
                /\ vv.ballot = b
                /\ vv.value  = v )
          => ( \A a2 \in Acceptor, vv2 \in Votes[a2] :
                vv2.ballot = b => vv2.value = v )
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

(* ---------------------------------------------------------------------- *)
(*  Chosen values: a value is chosen if some quorum has all its members
    voted for it in the same ballot                                         *)
Chosen ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E vv \in Votes[a] :
                    /\ vv.ballot = b
                    /\ vv.value  = v }

(* ---------------------------------------------------------------------- *)
(*  Property expressing consensus: at most one value can be chosen        *)
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

(* ---------------------------------------------------------------------- *)
(*  Symmetry: identity permutation on Acceptor (trivial symmetry)        *)
MCSymmetry == { [a \in Acceptor |-> a] }

====