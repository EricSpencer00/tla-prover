---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(* The set of possible element values *)
Values == {A, B, C}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES s, i, cand, cnt

(*--------------------------------------------------------------------
  Bounded sequence operator (as a function from 1..len to Values)
--------------------------------------------------------------------*)
SeqBounded(n) == [j \in 1..n |-> CHOOSE v \in Values : TRUE]

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ i   = 1
    /\ cnt = 0
    /\ cand \in Values
    /\ s \in [1..bound -> Values]

(*--------------------------------------------------------------------
  Next-state relation (Boyer-Moore scan step)
--------------------------------------------------------------------*)
Next ==
    \/ /\ i <= bound
       /\ LET x == s[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
          ELSE IF cand = x THEN
              /\ cnt' = cnt + 1
              /\ UNCHANGED cand
          ELSE
              /\ cnt' = cnt - 1
              /\ UNCHANGED cand
       /\ i' = i + 1
       /\ UNCHANGED s
    \/ /\ i > bound
       /\ UNCHANGED <<s, i, cand, cnt>>

Spec == Init /\ [][Next]_<<s, i, cand, cnt>>

(*--------------------------------------------------------------------
  Actions (aliases for use in the cfg if needed)
--------------------------------------------------------------------*)
InitAction == Init
NextAction == Next

(*--------------------------------------------------------------------
  Safety property: correct majority after full scan
--------------------------------------------------------------------*)
IsMajority(v) ==
    \A v2 \in Values :
        Cardinality({j \in 1..bound : s[j] = v}) >
        Cardinality({j \in 1..bound : s[j] = v2})

Correct ==
    (i > bound) => ( \E v \in Values : IsMajority(v) /\ v = cand )

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ s \in [1..bound -> Values]
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*--------------------------------------------------------------------
  Inductive invariant (captures the invariant maintained by the algo)
--------------------------------------------------------------------*)
Inv ==
    (i > bound) => (cnt = 0 \/ IsMajority(cand))

(*--------------------------------------------------------------------
  Liveness: eventual completion (optional, not used directly in .cfg)
--------------------------------------------------------------------*)
Completion == <> (i > bound)

=============================================================================