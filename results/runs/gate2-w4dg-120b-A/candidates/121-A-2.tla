---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

Entry == Nat \cup {0}
Sentinel == 0

VARIABLES str, n, failure, pmtch, i, best, pc
vars == <<str, n, failure, pmtch, i, best, pc>>

\* Zero-indexed strings: the character at position k of the rotation at
\* offset o is str[(k + o) % n].
RotChar(o, k) == str[(k + o) % n]

Corpus == [1..Nat -> STRING(CharacterSet)]

TypeInvariant ==
  /\ str \in Corpus
  /\ n = Len(str)
  /\ n >= 1
  /\ failure \in [0..(2 * n) - 1 -> Entry]
  /\ pmtch \in Entry
  /\ i \in 1..(2 * n)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "compare", "post", "next", "final"}

Init ==
  /\ \E s \in Corpus : str' = s
  /\ n' = Len(str)
  /\ failure' = [k \in 0..(2 * n) - 1 |-> Sentinel]
  /\ pmtch' = Sentinel
  /\ i' = 1
  /\ best' = 0
  /\ pc' = "outer"

\* 1. Outer loop check, counting past the doubled string length.
Outer ==
  /\ pc = "outer"
  /\ (i < 2 * n /\ pc' = "lookup")
  /\ (i >= 2 * n /\ pc' = "final")
  /\ UNCHANGED <<str, n, failure, pmtch, i, best>>

\* 2. Failure function lookup for the current position relative to best.
Lookup ==
  /\ pc = "lookup"
  /\ pmtch' = failure[i - 1]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, n, failure, i, best>>

\* 3. Inner loop: compare the current character with its candidate.
Compare ==
  /\ pc = "compare"
  /\ RotChar(best, i) # RotChar(0, i)
  /\ \/ pmtch # Sentinel
     \/ pc' = "post"
  /\ IF RotChar(0, i) < RotChar(best, i)
       THEN best' = i % n
       ELSE best' = best
  /\ pmtch' = IF pmtch # Sentinel
                THEN failure[pmtch - 1]
                ELSE pmtch
  /\ PCGuard("post")
  /\ UNCHANGED <<str, n, failure, i>>

\* 6. Post-comparison, after inner-loop exit.
Post ==
  /\ pc = "post"
  /\ RotChar(best, i) # RotChar(0, i)
  /\ pmtch = Sentinel
  /\ IF RotChar(0, i) < RotChar(best, i)
       THEN best' = i % n
       ELSE best' = best
  /\ failure' = [failure EXCEPT ![i - 1] = IF pmtch = Sentinel
                                         THEN Sentinel
                                         ELSE pmtch + 1]
  /\ pmtch' = Sentinel
  /\ PCGuard("next")
  /\ UNCHANGED <<str, n, i>>

Next ==
  \/ Outer
  \/ Lookup
  \/ Compare
  \/ Post
  \/ NextStep
  \/ Stutter

\* 7. Increment the loop counter and return to the outer check.
NextStep ==
  /\ pc = "next"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, failure, pmtch, best>>

PCGuard(t) ==
  /\ pc' = t
  /\ UNCHANGED <<str, n, failure, pmtch, i, best>>

Stutter ==
  /\ pc = "final"
  /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(NextStep)

\* Correctness: the best offset yields the lexicographically-minimal
\* rotation of the input, and tied rotations are broken by smallest offset.
Correctness ==
  /\ \A j \in 1..(n - 1) : RotChar(best, j) >= RotChar(best, 0)
  /\ \A j \in 1..(n - 1) : RotChar(best, j) = RotChar(best, 0) => j >= best

Termination == <>(pc = "final")

====