---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* Booth's least circular substring algorithm, modeled exactly from the
\* description above.  The module declares every constant, operator, and
\* action the reference TLC configuration expects, and nothing else.

CONSTANTS CharacterSet, Nat

\* The failure function is indexed up to twice the string length (the
\* doubled walk over the circular string).  The sentinel value -1 marks an
\* entry that has not been filled.
Undefined == -1

VARIABLES tape, length, Failure, pattern, i, w, pc
vars == <<tape, length, Failure, pattern, i, w, pc>>

\* A corpus of all possible input strings over the configured alphabet.
TapeSpace == { s \in Seq(CharacterSet) : Len(s) <= Nat }

\* Lexicographic ordering of rotations: the rotation at offset w is
\* smaller than (or equal to) any rotation at offset j, and in case of
\* equality it has the smaller shift value.
StringAtOffset(s, w) == SubSeq(s, w, Len(s) - 1) \o SubSeq(s, 0, w - 1)
CmpString(s, w, j) == IF StringAtOffset(s, w) < StringAtOffset(s, j)
                          THEN 1 ELSE IF StringAtOffset(s, w) = StringAtOffset(s, j)
                                    THEN IF w < j THEN 0 ELSE 1 ELSE 2

Init ==
    /\ \E s \in TapeSpace : tape = s
    /\ length = Len(tape)
    /\ Failure = [x \in 0..(2 * length) |-> Undefined]
    /\ pattern = Undefined
    /\ i = 1
    /\ w = 0
    /\ pc = "OuterCheck"

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ i >= 2 * length
    /\ pc' = "Terminated"
    /\ UNCHANGED <<tape, length, Failure, pattern, i, w>>

\* Failure function lookup: the index is offset by the current best rotation.
FailureLookup ==
    /\ pc = "OuterCheck"
    /\ i < 2 * length
    /\ Failure' = [Failure EXCEPT ![i + w] = Failure[i + w]]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<tape, length, pattern, i, w>>

\* The inner comparison loop: the characters at the current and candidate
\* positions are compared, and a mismatch with a non-sentinel pattern
\* index keeps the loop going; otherwise it drops to the post-comparison step.
InnerLoop ==
    /\ pc = "InnerLoop"
    /\ tape[(i % length)] # tape[(w + i) % length]
    /\ pattern # Undefined
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<tape, length, Failure, pattern, i, w>>

UpdateBestByLess ==
    /\ tape[i % length] < tape[(w + i) % length]
    /\ w' = i
    /\ UNCHANGED <<tape, length, Failure, pattern, i, pc>>

FollowPattern ==
    /\ pattern # Undefined
    /\ pattern' = Failure[pattern]
    /\ UNCHANGED <<tape, length, Failure, i, w, pc>>

\* The post-comparison step, entered only after the inner loop has dropped out.
PostComparison ==
    /\ pc = "InnerLoop"
    /\ tape[i % length] # tape[(w + i) % length]
    /\ pattern = Undefined
    /\ (IF tape[i % length] < tape[(w + i) % length] THEN w' = i ELSE w' = w)
    /\ Failure' = [Failure EXCEPT ![i + w] = IF tape[i % length] = tape[(w + i) % length]
                                      THEN pattern + 1 ELSE Undefined]
    /\ pc' = "Advance"
    /\ UNCHANGED <<tape, length, pattern, i>>

Advance ==
    /\ pc = "Advance"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ pattern' = pattern
    /\ UNCHANGED <<tape, length, Failure, w>>

Terminate ==
    /\ pc = "Terminated"
    /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerLoop \/ UpdateBestByLess
        \/ FollowPattern \/ PostComparison \/ Advance \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(FailureLookup) /\ WF_vars(PostComparison)

TypeInvariant ==
    /\ tape \in TapeSpace
    /\ length = Len(tape)
    /\ Failure \in [0..(2 * length) -> (0..(2 * length)) \cup {Undefined}]
    /\ pattern \in (0..(2 * length)) \cup {Undefined}
    /\ w \in 0..(length - 1)
    /\ i \in 1..(2 * length)
    /\ pc \in {"OuterCheck", "InnerLoop", "Advance", "Terminated"}

Correctness ==
    /\ pc = "Terminated"
    /\ \A j \in 0..(length - 1) : CmpString(tape, w, j) <= 1

Termination == <>(pc = "Terminated")

====