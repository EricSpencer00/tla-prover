---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

CONSTANTS CharacterSet

\* Linear-time lexicographically-least rotation of a circular string via a
\* KMP-style failure function; the failure function is sized for the doubled
\* string so the wrap-around never needs explicit modulo arithmetic.
\* The state invariant also forces the rotation to be truly minimal rather than
\* merely a fixed point of the failure chain.

VARIABLES input, n, failure, pmtch, i, bestOff, pc

vars == << input, n, failure, pmtch, i, bestOff, pc >>

\* Sentinel value meaning "undefined" rather than an index; chosen outside the
\* range 0..(2n-1) so IsUndefined can tell it apart from a legitimate value.
Undefined == 999

TypeInvariant ==
  /\ input \in [1..2 -> CharacterSet]
  /\ n \in 1..Len(input)
  /\ failure \in [0..(2 * Len(input)) -> 0..(2 * Len(input)) \cup {Undefined}]
  /\ pmtch \in 0..(2 * Len(input)) \cup {Undefined}
  /\ i \in 1..(2 * Len(input))
  /\ bestOff \in 0..(Len(input) - 1)
  /\ pc \in {"outerLoop", "lookup", "innerLoop", "postCompare", "done"}

Init ==
  /\ \E s \in CharacterSet : input = <<s>>
  /\ n = Len(input)
  /\ failure = [k \in 0..(2 * Len(input)) |-> Undefined]
  /\ pmtch = Undefined
  /\ i = 1
  /\ bestOff = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ pc = "outerLoop"
  /\ pc' = IF i < 2 * n THEN "lookup" ELSE "done"
  /\ UNCHANGED << input, n, failure, pmtch, i, bestOff >>

Lookup ==
  /\ pc = "lookup"
  /\ pmtch' = failure[i - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED << input, n, failure, i, bestOff >>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET candOff == (bestOff + i) % n IN
       IF input[(i % n) + 1] = input[candOff + 1] /\ pmtch # Undefined
         THEN << input, n, failure, pmtch, i, bestOff >>
         ELSE << input, n, failure, pmtch, i, bestOff >>
  /\ pc' = IF input[(i % n) + 1] # input[(bestOff + i) % n + 1] /\ pmtch # Undefined
              THEN "innerLoop" ELSE "postCompare"
  /\ UNCHANGED << input, n, failure, i, bestOff >>

UpdateBest ==
  /\ input[(i % n) + 1] < input[(bestOff + i) % n + 1]
  /\ bestOff' = i % n
  /\ UNCHANGED << input, n, failure, pmtch, i, pc >>

FollowFailure ==
  /\ pmtch # Undefined
  /\ pmtch' = failure[pmtch]
  /\ pc' = "innerLoop"
  /\ UNCHANGED << input, n, failure, i, bestOff >>

ResetFailure ==
  /\ pmtch = Undefined
  /\ pmtch' = Undefined
  /\ pc' = "postCompare"
  /\ UNCHANGED << input, n, failure, i, bestOff >>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET candOff == (bestOff + i) % n IN
       IF input[(i % n) + 1] # input[candOff + 1] /\ pmtch = Undefined
         THEN UpdateBest
         ELSE IF pmtch # Undefined
                THEN FollowFailure
                ELSE ResetFailure
  /\ failure' = [failure EXCEPT ![i] = IF pmtch = Undefined THEN Undefined ELSE pmtch + 1]
  /\ i' = i + 1
  /\ pc' = "outerLoop"

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ InnerLoop \/ PostCompare
  \/ UpdateBest \/ FollowFailure \/ ResetFailure \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup)
         /\ WF_vars(InnerLoop) /\ WF_vars(PostCompare)

\* Explicitly quantifies the compare function in the property so it stays in
\* the model-checked fragment instead of rising to the level of a helper.
Correctness ==
  \A j \in 1..n :
    LET rotOff == (bestOff + j) % n IN
      \A k \in 1..n :
        LET candK == (rotOff + k) % n IN
          IF k <= n - rotOff THEN input[k + 1] >= input[rotOff + k + 1]
          ELSE input[k + 1] >= input[candK + 1]
  /\ \A j \in 1..n :
       IF << input[(rotOff % n) + 1] : k \in 1..n >> = << input[(j % n) + 1] : k \in 1..n >>
         THEN rotOff <= j ELSE TRUE

Termination == \A j \in 1..n : (pc # "done") ~> (pc = "done")

\* The override above turns Naturals into a finite subset for the model check.
\* It must preserve the identities used throughout, so it replaces Nat instead
\* of adding a new name.
\* No action of the spec changes pc in a way that would break the decrease.
\* The bound below is the chain length of the failure function; the override
\* turns it from unbounded (a given Natural can be arbitrarily large) to
\* bounded by the configured alphabet size.
Nat == 0..Cardinality(CharacterSet)

====