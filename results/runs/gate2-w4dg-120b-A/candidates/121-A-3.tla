---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* Booth's least-circular-substring algorithm, modeled after the description
\* above.  The implementation uses zero-indexed sequences (not the standard
\* one-indexed ones) and tracks every variable the description names, with
\* the same names.
CONSTANTS
  CharacterSet
  Nat

\* The input string is a nondeterministic choice from every zero-indexed
\* sequence over CharacterSet up to the configured maximum length.
\* In a model-checking run the character set size and the maximum length
\* are set in the .cfg file (the CONSTANTS line above).
Corpus == [i \in 0..Nat : CharacterSet]

\* Sentinel value for an undefined failure-function entry.
Undefined == Nat + 1

VARIABLES
  inputString
  length
  fail
  pat
  outer
  offset
  pc

vars == <<inputString, length, fail, pat, outer, offset, pc>>

\* The rotation at offset k is the string read from inputString[k..] then
\* inputString[0..k-1]; the lexicographic comparison runs index by index.
Rotation(k, i) == inputString[(k + i) % length]

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ fail = [i \in 0..(2 * length) |-> Undefined]
  /\ pat = Undefined
  /\ outer = 1
  /\ offset = 0
  /\ pc = "outerCheck"

\* The outer loop runs up to (but not including) twice the string length,
\* which is exactly the number of characters examined by Booth's algorithm
\* on a doubled string.
OuterCheck ==
  /\ pc = "outerCheck"
  /\ outer < 2 * length
  /\ pc' = "lookupFail"
  /\ UNCHANGED <<inputString, length, fail, pat, outer, offset>>

LookupFail ==
  /\ pc = "lookupFail"
  /\ fail' = [fail EXCEPT ![outer] = fail[(outer + offset) % length]]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, pat, outer, offset>>

\* The inner loop compares the character at the current loop position
\* against the one at the candidate position; pat holds the current
\* failure-function index (or the sentinel if none).
Compare ==
  /\ pc = "compare"
  /\ \/ (Rotation(outer, 0) # Rotation(offset, 0) /\ pat # Undefined)
     \/ (Rotation(outer, 0) = Rotation(offset, 0))
  /\ pc' = IF Rotation(outer, 0) # Rotation(offset, 0) /\ pat # Undefined
           THEN "compare"
           ELSE "post"
  /\ UNCHANGED <<inputString, length, fail, pat, outer, offset>>

UpdateOffset ==
  /\ pc = "compare"
  /\ Rotation(outer, 0) < Rotation(offset, 0)
  /\ offset' = outer
  /\ UNCHANGED <<inputString, length, fail, pat, outer, pc>>

FollowFail ==
  /\ pc = "compare"
  /\ pat' = fail[outer]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, fail, outer, offset>>

PostComparison ==
  /\ pc = "post"
  /\ IF Rotation(outer, 0) # Rotation(offset, 0) /\ pat = Undefined
     THEN offset' = IF Rotation(outer, 0) < Rotation(offset, 0) THEN outer ELSE offset
     ELSE offset' = offset
  /\ fail' = [fail EXCEPT ![outer] = IF Rotation(outer, 0) # Rotation(offset, 0)
                                          /\ pat = Undefined
                                      THEN Undefined
                                      ELSE pat + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, pat, outer>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, length, fail, pat, offset>>

Terminate ==
  /\ pc = "outerCheck"
  /\ outer >= 2 * length
  /\ pc' = "done"
  /\ UNCHANGED <<inputString, length, fail, pat, outer, offset>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ LookupFail
  \/ Compare
  \/ UpdateOffset
  \/ FollowFail
  \/ PostComparison
  \/ Increment
  \/ Terminate
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment) /\ WF_vars(Terminate)

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ \A i \in 0..(2 * length) : fail[i] \in 0..(2 * length) \cup {Undefined}
  /\ pat \in 0..(2 * length) \cup {Undefined}
  /\ outer \in 0..(2 * length)
  /\ offset \in 0..(length - 1)
  /\ pc \in {"outerCheck", "lookupFail", "compare", "post", "increment", "done"}

\* Correctness: on termination the best rotation offset is the shift of the
\* lexicographically-minimal rotation, and among rotations with the same
\* string it is the smallest shift value.
Correctness ==
  /\ pc = "done"
  /\ \A k \in 0..(length - 1) : Rotation(offset, 0) <= Rotation(k, 0)
  /\ \A k \in 0..(length - 1) : Rotation(offset, 0) = Rotation(k, 0) => offset <= k

Termination == <>(pc = "done")

====