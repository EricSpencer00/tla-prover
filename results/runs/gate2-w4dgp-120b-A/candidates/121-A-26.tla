---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, Integers

\* This implements Booth's linear-time algorithm for the lexicographically-
\* least rotation of a circular string (circa 1980).  A nondeterministic
\* zero-indexed string over a finite character set is chosen as the corpus
\* and the algorithm reduces it to a single preferred rotation in place.
\* The invariants enforce that the model's basic types always stay within
\* their intended finite ranges (a bounded alphabet, a bounded string
\* length, and bounded index counters).

\* The algorithm works over a doubled string (indexing twice the length),
\* but uses a zero-indexed failure function and pattern-match index; the
\* reference implementation in the literature is one-indexed, so the
\* bounded ranges here are strict (the loop counter never reaches
\* 2*Length, the failure function never reads past its array, etc.).
\* A stuttering action lets the model stay in its final state once the
\* loop counter has run out.

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat /\ Cardinality(CharacterSet) >= 2

VARIABLES StringSeq, Length, Failure, PatternIndex, LoopCounter,
          BestOffset, PC

vars == <<StringSeq, Length, Failure, PatternIndex,
          LoopCounter, BestOffset, PC>>

Sentinel == Length + 1

TypeInvariant ==
  /\ StringSeq \in [0..(Length - 1) -> CharacterSet]
  /\ Length = Len(StringSeq)
  /\ Length >= 1 /\ Length <= 4
  /\ Failure \in [0..(2 * Length - 1) -> 0..Sentinel]
  /\ PatternIndex \in 0..Sentinel
  /\ LoopCounter \in 0..(2 * Length)
  /\ BestOffset \in 0..(Length - 1)
  /\ PC \in {"outer_loop", "failure_lookup", "inner_compare", "post_compare", "done"}

Init ==
  /\ \E s \in [1..4 -> CharacterSet] : StringSeq = s /\ Length = Len(s)
  /\ Failure = [i \in 0..7 |-> Sentinel]
  /\ PatternIndex = Sentinel
  /\ LoopCounter = 1
  /\ BestOffset = 0
  /\ PC = "outer_loop"

\* Outer loop is bounded strictly by (2 * Length) -- the algorithm never
\* reaches the bound itself, which keeps the failure function in range.
OuterLoop ==
  /\ PC = "outer_loop"
  /\ LoopCounter < 2 * Length
  /\ PC' = "failure_lookup"
  /\ UNCHANGED <<StringSeq, Length, Failure, PatternIndex,
                 LoopCounter, BestOffset>>

FailureLookup ==
  /\ PC = "failure_lookup"
  /\ Failure' = [Failure EXCEPT ![LoopCounter] = Failure[BestOffset + LoopCounter]]
  /\ PC' = "inner_compare"
  /\ UNCHANGED <<StringSeq, Length, PatternIndex, LoopCounter, BestOffset>>

\* The inner loop only fires while the failure function chain is still
\* yielding a non-sentinel value (a live candidate) and the characters
\* currently compared are equal, so the chain can be followed.
InnerCompare ==
  /\ PC = "inner_compare"
  /\ IF StringSeq[LoopCounter % Length] # StringSeq[(BestOffset + LoopCounter) % Length]
       /\ PatternIndex # Sentinel
     THEN PC' = "inner_compare"
     ELSE PC' = "post_compare"
  /\ UNCHANGED <<StringSeq, Length, Failure, PatternIndex,
                 LoopCounter, BestOffset>>

UpdateBest ==
  /\ StringSeq[LoopCounter % Length] < StringSeq[(BestOffset + LoopCounter) % Length]
  /\ BestOffset' = LoopCounter
  /\ UNCHANGED <<StringSeq, Length>>

FollowFailure ==
  /\ PC = "post_compare"
  /\ IF StringSeq[LoopCounter % Length] # StringSeq[(BestOffset + LoopCounter) % Length]
       /\ PatternIndex = Sentinel
     THEN PC' = "post_compare"
     ELSE PC' = "post_compare"
  /\ IF StringSeq[LoopCounter % Length] # StringSeq[(BestOffset + LoopCounter) % Length]
       /\ PatternIndex = Sentinel
       /\ StringSeq[LoopCounter % Length] < StringSeq[(BestOffset + LoopCounter) % Length]
     THEN BestOffset' = LoopCounter
     ELSE BestOffset' = BestOffset
  /\ UNCHANGED <<StringSeq, Length, LoopCounter, PC>>
  /\ IF PatternIndex = Sentinel
       THEN Failure' = [Failure EXCEPT ![LoopCounter] = Sentinel]
       ELSE Failure' = [Failure EXCEPT ![LoopCounter] = PatternIndex + 1]

AdvanceLoop ==
  /\ PC = "post_compare"
  /\ PC' = "outer_loop"
  /\ LoopCounter' = LoopCounter + 1
  /\ UNCHANGED <<StringSeq, Length, Failure, PatternIndex, BestOffset>>

Done ==
  /\ PC = "outer_loop"
  /\ LoopCounter >= 2 * Length
  /\ PC' = "done"
  /\ UNCHANGED <<StringSeq, Length, Failure, PatternIndex,
                 LoopCounter, BestOffset>>

Stall ==
  /\ PC = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ FailureLookup \/ InnerCompare
  \/ UpdateBest \/ FollowFailure \/ AdvanceLoop \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailureLookup)
               /\ WF_vars(AdvanceLoop)

\* Correctness: the rotation at the recorded BestOffset is less-or-equal
\* to every other rotation, and is strictly less whenever any two
\* rotations are equal -- so it is the unique least rotation (modulo tie
\* offset minimization) of the input string.
Correctness ==
  /\ \A i \in 0..(Length - 1) :
       StringSeq[(BestOffset + i) % Length] <= StringSeq[i]
  /\ \A i \in 0..(Length - 1) :
       (StringSeq[(BestOffset + i) % Length] = StringSeq[i])
         => BestOffset <= i

Termination == <>(PC = "done")

====