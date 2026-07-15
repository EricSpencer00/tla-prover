---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, i, cand, cnt

(* ------------------------------------------------------------------------- *)
(* Types / Set definitions                                                   *)
(* ------------------------------------------------------------------------- *)

Values == {A, B, C}

(* Sequences of length 0..bound over Values *)
SeqBound == { s \in [1..n -> Values] : n \in 0..bound \/
                                    (n = 0 /\ DOMAIN s = {}) }

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand = A               \* any element of Values; choice does not affect correctness
    /\ cnt = 0

(* ------------------------------------------------------------------------- *)
(* Step actions                                                             *)
(* ------------------------------------------------------------------------- *)

AddToSeq ==
    /\ i < bound
    /\ i' = i + 1
    /\ cnt' = IF i = 0 THEN 1 ELSE
                IF seq[i] = seq[i'] THEN cnt + 1
                ELSE IF cnt = 1 THEN 1
                ELSE cnt - 1
    /\ cand' = IF i = 0 THEN seq[1]
                ELSE IF seq[i] = cand THEN cand
                ELSE IF cnt = 1 THEN seq[i+1]
                ELSE cand
    /\ seq' = [seq EXCEPT ![i+1] = Values \ {cand, seq[i]} \ {A, B, C}] \* placeholder; actual value nondeterministic over Values
    /\ UNCHANGED << >>

Next ==
    \/ AddToSeq
    \/ UNCHANGED << seq, i, cand, cnt >>

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>>

(* ------------------------------------------------------------------------- *)
(* Invariant: after sequence is built (i = bound), cand is a majority element *)
(* ------------------------------------------------------------------------- *)

MajorityInv ==
    (i = bound) => 
        \A v \in Values : 
            ( Cardinality({j \in 1..bound : seq[j] = v}) > bound / 2 ) => v = cand

=============================================================================