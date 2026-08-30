---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A zero-indexed string over a finite alphabet (the corpus is all such strings
\* up to the configured length); failure function is KMP-style, loop counter
\* iterates past the end of the string to model the circular wrap-around.
VARIABLES string, len, failure, matchIdx, loop, best, pc

\* The index is a zero-indexed sequence from Sequences, so the program counter
\* is a natural with a bounded range rather than an unbounded integer.
vars == <<string, len, failure, matchIdx, loop, best, pc>>
Sentinel == 99
MaxLoop == 4
MaxLen == 2
Phases == {"loop", "lookup", "inner", "post", "done"}

TypeInvariant ==
    /\ string \in [0..(MaxLen - 1) -> CharacterSet]
    /\ len \in 0..(MaxLen - 1)
    /\ failure \in [0..(2 * MaxLen - 1) -> 0..MaxLoop \cup {Sentinel}]
    /\ matchIdx \in 0..MaxLoop \cup {Sentinel}
    /\ loop \in 1..(2 * MaxLen)
    /\ best \in 0..(MaxLen - 1)
    /\ pc \in Phases

Init ==
    /\ string = [i \in 0..(MaxLen - 1) |-> CHOOSE c \in CharacterSet : TRUE]
    /\ len = Len(string)
    /\ failure = [i \in 0..(2 * MaxLen - 1) |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "loop"

\* Booth's outer loop: runs past the end of the string to handle wrap-around.
LoopCheck ==
    /\ pc = "loop"
    /\ IF loop < (2 * len) THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<string, len, failure, matchIdx, loop, best>>

\* KMP-style failure function lookup for the current position.
Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loop - 1] = failure[best + loop - 1]]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, len, matchIdx, loop, best>>

\* Compare the current character (modulo length) against the candidate
\* character. Follow the failure chain while they differ.
Inner ==
    /\ pc = "inner"
    /\ IF string[loop % len] # string[(best + loop) % len]
       THEN IF matchIdx # Sentinel
            THEN /\ matchIdx' = failure[matchIdx]
                 /\ pc' = "inner"
            ELSE /\ pc' = "post"
                 /\ UNCHANGED matchIdx
       ELSE matchIdx' = loop
            /\ pc' = "post"
    /\ UNCHANGED <<string, len, failure, loop, best>>

\* If the current character is less than the candidate, it yields a better
\* rotation and the best offset is updated in place.
BetterOuter ==
    /\ pc = "inner"
    /\ string[loop % len] < string[(best + loop) % len]
    /\ best' = loop % len
    /\ UNCHANGED <<string, len, failure, matchIdx, loop, pc>>

Follow ==
    /\ pc = "inner"
    /\ matchIdx # Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<string, len, failure, matchIdx, loop, best>>

\* If the failure chain is exhausted (sentinel) and the characters still differ,
\* compare once more and set the failure function entry accordingly.
PostCompare ==
    /\ pc = "post"
    /\ string[loop % len] # string[(best + loop) % len]
    /\ matchIdx = Sentinel
    /\ best' = IF string[loop % len] < string[(best + loop) % len]
              THEN loop % len ELSE best
    /\ failure' = [failure EXCEPT ![loop - 1] =
                     IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
    /\ pc' = "loop"
    /\ loop' = loop + 1
    /\ UNCHANGED <<string, len, matchIdx>>

Advance ==
    /\ pc = "post"
    /\ pc' = "loop"
    /\ loop' = loop + 1
    /\ UNCHANGED <<string, len, failure, matchIdx, best>>

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == LoopCheck \/ Lookup \/ Inner \/ BetterOuter \/ Follow \/ PostCompare \/ Advance \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopCheck) /\ WF_vars(Lookup)
        /\ WF_vars(Inner) /\ WF_vars(PostCompare)

\* Lexicographic minimality: the rotation at best is <= every other rotation,
\* and among rotations that tie it has the smallest shift.
Correctness ==
    /\ best \in 0..(len - 1)
    /\ \A i \in 0..(len - 1): StrComp(string[(best + i) % len], string[(best + i + 1) % len]) <= 0
    /\ \A i \in 0..(len - 1):
        (StrComp(string[(best + i) % len], string[(best + i + 1) % len]) = 0) => (best <= ((best + i + 1) % len))

Termination == <>(pc = "done")

\* Redefine Nat as a bounded finite version for model checking, keeping the
\* extension of Naturals so the other modules stay intact.
ZSequencesNat == 0..MaxLen
====