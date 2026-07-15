---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS CharacterSet, Nat

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
Sentinel == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES input, n, pi, s, i, offset, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
InputSet == { s \in Seq(CharacterSet) : Len(s) <= Nat }

Chars == input[i % n + 1]
CandChars == input[(offset + i) % n + 1]

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
  /\ input \in InputSet
  /\ n = Len(input)
  /\ n > 0
  /\ pi = [j \in 0..(2 * n - 1) |-> Sentinel]
  /\ s = Sentinel
  /\ i = 1
  /\ offset = 0
  /\ pc = "OuterLoopCheck"

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
OuterLoopCheck ==
  /\ pc = "OuterLoopCheck"
  /\ IF i < 2 * n
        THEN pc' = "FailureLookup"
        ELSE pc' = "Terminate"
  /\ UNCHANGED <<input, n, pi, s, i, offset>>

FailureLookup ==
  /\ pc = "FailureLookup"
  /\ s' = pi[(offset + i) % n]
  /\ pc' = "InnerCompare"
  /\ UNCHANGED <<input, n, pi, i, offset>>

InnerCompare ==
  /\ pc = "InnerCompare"
  /\ IF s # Sentinel
        THEN /\ IF Chars = CandChars
                THEN /\ s' = pi[s]
                     /\ pc' = "InnerCompare"
                ELSE /\ pc' = "PostComparison"
        ELSE /\ pc' = "PostComparison"
  /\ UNCHANGED <<input, n, pi, i, offset, s>>

PostComparison ==
  /\ pc = "PostComparison"
  /\ IF s = Sentinel
        THEN /\ IF Chars = CandChars
                THEN /\ pi' = [pi EXCEPT ![(offset + i) % n] = s + 1]
                     /\ offset' = offset
                ELSE /\ pi' = [pi EXCEPT ![(offset + i) % n] = Sentinel]
                     /\ offset' = offset
        ELSE /\ IF Chars < CandChars
                THEN /\ offset' = (i - s) % n
                ELSE offset' = offset
             /\ pi' = [pi EXCEPT ![(offset + i) % n] = s + 1]
  /\ i' = i + 1
  /\ s' = Sentinel
  /\ pc' = "OuterLoopCheck"
  /\ UNCHANGED <<input, n>>

Terminate ==
  /\ pc = "Terminate"
  /\ UNCHANGED <<input, n, pi, s, i, offset, pc>>

Stutter ==
  /\ pc = "Terminate"
  /\ UNCHANGED <<input, n, pi, s, i, offset, pc>>

Next ==
  \/ OuterLoopCheck
  \/ FailureLookup
  \/ InnerCompare
  \/ PostComparison
  \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<input, n, pi, s, i, offset, pc>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ input \in InputSet
  /\ n = Len(input)
  /\ n > 0
  /\ pi \in [0..(2 * n - 1) -> (0..(n - 1) \cup {Sentinel})]
  /\ s \in (0..(n - 1)) \cup {Sentinel}
  /\ i \in 0..(2 * n)
  /\ offset \in 0..(n - 1)

(*--------------------------------------------------------------------
  Correctness invariant (safety)
--------------------------------------------------------------------*)
Correctness ==
  \A k \in 0..(n - 1) :
    \A j \in 1..(n - 1) :
      LET rot1 == << input[(offset + k) % n + 1] : k \in 0..(n - 1) >>
          rot2 == << input[(offset + j) % n + 1] : j \in 0..(n - 1) >>
      IN (rot1 # rot2) => (rot1 <_lex rot2)

(*--------------------------------------------------------------------
  Termination liveness property
--------------------------------------------------------------------*)
Termination == <> (pc = "Terminate")

====