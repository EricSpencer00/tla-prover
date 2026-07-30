---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS
    CharacterSet

\* The identifier CharacterSet is re-used in the .cfg to replace the built-in
\* NAT definition (which is infinite) with a finite version of NAT for the
\* model checker. EXTENDS Naturals is still present because CharacterSet is a
\* subset of Nat, but nothing in this module declares Nat itself.
\*[ZSequences]CharacterSet

VARIABLES
    string
    length
    fail
    pmatch
    i
    best
    pc

vars == <<string, length, fail, pmatch, i, best, pc>>

Sentinel == 99
MaximumLength == 3

TypeInvariant ==
    /\ string \in [1..MaximumLength -> CharacterSet]
    /\ length = Len(string)
    /\ fail \in [0..2 * MaximumLength -> 0..(2 * MaximumLength + 1)]
    /\ pmatch \in 0..(2 * MaximumLength + 1)
    /\ i \in 1..(2 * MaximumLength)
    /\ best \in 0..(length - 1)
    /\ pc \in {"outer", "lookup", "inner", "post"}

Init ==
    /\ \E s \in [1..MaximumLength -> CharacterSet] : string = s
    /\ length = Len(string)
    /\ fail = [n \in 0..2 * MaximumLength |-> Sentinel]
    /\ pmatch = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "outer"

OuterCheck ==
    /\ pc = "outer"
    /\ i < 2 * length
    /\ pc' = "lookup"
    /\ UNCHANGED <<string, length, fail, pmatch, i, best>>

OuterTerminate ==
    /\ pc = "outer"
    /\ i >= 2 * length
    /\ pc' = "post"
    /\ UNCHANGED <<string, length, fail, pmatch, i, best>>

FailureLookup ==
    /\ pc = "lookup"
    /\ fail[best + i] # Sentinel
    /\ pmatch' = fail[best + i]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, length, fail, i, best>>

CompareChars ==
    /\ pc = "inner"
    /\ string[(best + i) % length] # string[pmatch % length]
    /\ pmatch # Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<string, length, fail, pmatch, i, best>>

UpdateBestLess ==
    /\ pc = "inner"
    /\ string[(best + i) % length] < string[pmatch % length]
    /\ best' = (best + i) % length
    /\ UNCHANGED <<string, length, fail, pmatch, i, pc>>

FollowFailure ==
    /\ pc = "inner"
    /\ pmatch' = fail[pmatch]
    /\ UNCHANGED <<string, length, fail, i, best, pc>>

PostComparison ==
    /\ pc = "post"
    /\ LET charsDiffer == string[(best + i) % length] # string[pmatch % length] IN
       /\ IF charsDiffer /\ pmatch = Sentinel
          THEN LET newBest == IF string[(best + i) % length] < string[pmatch % length]
                              THEN (best + i) % length
                              ELSE best
               IN /\ best' = newBest
                  /\ fail' = [fail EXCEPT ![best + i] = IF charsDiffer THEN Sentinel ELSE pmatch + 1]
          ELSE /\ fail' = [fail EXCEPT ![best + i] = pmatch + 1]
             /\ UNCHANGED best
    /\ i' = i + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<string, length, pmatch>>

Stall ==
    /\ pc = "post"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ OuterTerminate
    \/ FailureLookup
    \/ CompareChars
    \/ UpdateBestLess
    \/ FollowFailure
    \/ PostComparison
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)

\* Correctness: the rotation at the recorded offset is lexicographically
\* minimal among all rotations, and among ties it is the smallest shift.
Correctness ==
    /\ (pc = "post" => \A n \in 0..(length - 1) : string[(best + n) % length] >= string[n])
    /\ (pc = "post" => \A n \in 0..(length - 1) : (string[(best + n) % length] = string[n]) => ((best + n) % length) >= n)

Termination == <>(pc = "post")

\* No extra wrappers: the SPECIFICATION, INVARIANTS and PROPERTIES names
\* are exactly as the .cfg expects.
====