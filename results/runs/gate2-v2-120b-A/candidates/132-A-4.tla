---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (set in the .cfg)
--------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived constant: the set of possible element values
--------------------------------------------------------------------*)
Values == {A, B, C}

(*--------------------------------------------------------------------
  State variables (inherited from the main majority vote spec)
--------------------------------------------------------------------*)
VARIABLES seq, p, candidate, counter

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
PosRange == 1 .. bound

SeqBounded ==
  { s \in [1 .. n -> Values] : n \in 0 .. bound }

(*--------------------------------------------------------------------
  Type predicate (used in the TypeOK invariant)
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in SeqBounded
  /\ p \in PosRange \cup {0}
  /\ candidate \in Values
  /\ counter \in Nat

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ seq \in SeqBounded
  /\ p = 1
  /\ candidate \in Values
  /\ counter = 0

(*--------------------------------------------------------------------
  Action: scan the next element (the Boyer-Moore update rules)
--------------------------------------------------------------------*)
Next ==
  \/ /\ p <= bound
     /\ LET cur == seq[p] IN
        IF counter = 0 THEN
          /\ candidate' = cur
          /\ counter'   = 1
        ELSE IF candidate = cur THEN
          /\ candidate' = candidate
          /\ counter'   = counter + 1
        ELSE
          /\ candidate' = candidate
          /\ counter'   = counter - 1
     /\ p' = IF p = bound THEN bound ELSE p + 1
     /\ UNCHANGED seq
  \/ /\ p > bound
     /\ UNCHANGED <<seq, p, candidate, counter>>

(*--------------------------------------------------------------------
  Overall specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, p, candidate, counter>>

(*--------------------------------------------------------------------
  Safety invariants required by the .cfg
--------------------------------------------------------------------*)
TypeOKInvariant == TypeOK

Correct ==
  /\ p > bound
  /\ \A x \in Values :
       (Cardinality({ i \in DOMAIN seq : seq[i] = x }) > bound / 2) => x = candidate

Inv == Correct

(*--------------------------------------------------------------------
  Liveness property (not required as an identifier, but included for
  completeness; the .cfg can reference it if desired)
--------------------------------------------------------------------*)
Completion == <> (p > bound)

=============================================================================