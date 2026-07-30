---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  CharacterSet

VARIABLES
  inputString
  strLen
  fnext
  pnext
  i
  best
  pc

vars == <<inputString, strLen, fnext, pnext, i, best, pc>>

\* The spec is meant to be checked under a module that defines the corpus of
\* admissible input strings; the spec only ever reads the input.
Corpus == [1..strLen -> CharacterSet]

MaxLen == 3
NoVal == MaxLen + 1

\* Zero-indexed sequences (ZSequences) are imported via the .cfg's operator
\* replacement: [ZSequences]CharacterSet replaces Naturals.
ZIndex(s, k) == s[(k % strLen) + 1]

Init ==
  /\ \E s \in Corpus : inputString = s
  /\ strLen = Len(inputString)
  /\ fnext = [k \in 0..(2 * MaxLen) |-> NoVal]
  /\ pnext = NoVal
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ IF i < 2 * strLen
     THEN pc' = "lookup"
     ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, fnext, pnext, i, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pnext' = fnext[i - best]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, fnext, i, best>>

Compare ==
  /\ pc = "compare"
  /\ ZIndex(inputString, i) # ZIndex(inputString, best)
  /\ pnext # NoVal
  /\ pc' = "continue"
  /\ UNCHANGED <<inputString, strLen, fnext, pnext, i, best>>

UpdateBestFromLoop ==
  /\ pc = "compare"
  /\ ZIndex(inputString, i) # ZIndex(inputString, best)
  /\ pnext = NoVal
  /\ ZIndex(inputString, i) < ZIndex(inputString, best)
  /\ best' = i
  /\ pc' = "follow"
  /\ UNCHANGED <<inputString, strLen, fnext, pnext, i>>

Follow ==
  /\ pc = "continue"
  /\ pnext' = fnext[pnext]
  /\ pc' = "post"
  /\ UNCHANGED <<inputString, strLen, fnext, i, best>>

PostComparison ==
  /\ pc = "post"
  /\ \/ (ZIndex(inputString, i) # ZIndex(inputString, best) /\ fnext[best] = NoVal)
        /\ LET cand == IF ZIndex(inputString, i) < ZIndex(inputString, best) THEN i ELSE best
           IN best' = cand
        /\ fnext' = [fnext EXCEPT ![i] = NoVal]
     \/ (ZIndex(inputString, i) # ZIndex(inputString, best) /\ fnext[best] # NoVal)
        /\ best' = best
        /\ fnext' = [fnext EXCEPT ![i] = pnext + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, pnext, i>>

Increment ==
  /\ pc = "increment"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, strLen, fnext, pnext, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ UpdateBestFromLoop
  \/ Follow
  \/ PostComparison
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
        /\ WF_vars(Compare) /\ WF_vars(UpdateBestFromLoop)
        /\ WF_vars(Follow) /\ WF_vars(PostComparison) /\ WF_vars(Increment)

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ fnext \in [0..(2 * MaxLen) -> 0..(MaxLen + 1)]
  /\ pnext \in 0..(MaxLen + 1)
  /\ i \in 1..(2 * MaxLen + 1)
  /\ best \in 0..MaxLen
  /\ pc \in {"outer", "lookup", "compare", "continue", "follow",
             "post", "increment", "done"}

RotLessOrEqual(s, o) ==
  \A k \in 1..strLen : s[(o + k - 1) % strLen + 1] <= s[(k - 1) % strLen + 1]

RotMinimal(s, o) ==
  \A k \in 1..strLen : s[(o + k - 1) % strLen + 1] <= s[(k - 1) % strLen + 1]
    /\ (s[(o + k - 1) % strLen + 1] = s[(k - 1) % strLen + 1]
        => o <= (k - 1) % strLen)

Correctness ==
  (pc = "done") => RotMinimal(inputString, best)

Termination ==
  <>(pc = "done")

====