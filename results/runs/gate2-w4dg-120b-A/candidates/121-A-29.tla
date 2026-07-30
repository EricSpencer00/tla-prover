---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

VARIABLES string, slen, fail, matchIdx, loop, bestOffset, pc

vars == <<string, slen, fail, matchIdx, loop, bestOffset, pc>>

Sentinel == -1

Rot(s) == SubSeq(s, s.len - s.start + 1, s.len) \o SubSeq(s, 1, s.len - s.start)

LessLex(a, b) ==
    IF a = b THEN FALSE
    ELSE \E k \in 1 .. Len(a) : \A j \in 1 .. k - 1 : a[j] = b[j] /\ a[k] < b[k]

TypeInvariant ==
    /\ string \in STRING(CharacterSet)
    /\ slen = Len(string)
    /\ fail \in [0 .. 2 * slen -> {Sentinel} \cup (0 .. 2 * slen)]
    /\ matchIdx \in {Sentinel} \cup (0 .. 2 * slen)
    /\ loop \in 1 .. 2 * slen
    /\ bestOffset \in 0 .. (slen - 1)
    /\ pc \in {"outer", "lookup", "inner", "reset", "post", "done"}

Init ==
    /\ string \in STRING(CharacterSet)
    /\ slen = Len(string)
    /\ fail = [i \in 0 .. 2 * slen |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loop = 1
    /\ bestOffset = 0
    /\ pc = "outer"

LoopCheck ==
    /\ pc = "outer"
    /\ IF loop < 2 * slen THEN pc' = "lookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<string, slen, fail, matchIdx, loop, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = fail[loop - bestOffset]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, slen, fail, loop, bestOffset>>

CharAt(i) == string[((i - 1) % slen) + 1]
Candidate(i) == string[((i - bestOffset - 1) % slen) + 1]

Compare ==
    /\ pc = "inner"
    /\ (CharAt(loop) # Candidate(loop) /\ matchIdx # Sentinel)
       \/ (CharAt(loop) = Candidate(loop) /\ matchIdx' = loop)
    /\ pc' = IF (CharAt(loop) # Candidate(loop) /\ matchIdx # Sentinel)
               THEN "inner"
               ELSE "post"
    /\ UNCHANGED <<string, slen, fail, loop, bestOffset>>

Jump ==
    /\ pc = "inner"
    /\ CharAt(loop) # Candidate(loop) /\ matchIdx # Sentinel
    /\ CharAt(loop) < Candidate(loop)
    /\ bestOffset' = loop - matchIdx
    /\ UNCHANGED <<string, slen, fail, matchIdx, loop, pc>>

Follow ==
    /\ pc = "inner"
    /\ matchIdx # Sentinel
    /\ matchIdx' = fail[matchIdx]
    /\ UNCHANGED <<string, slen, fail, loop, bestOffset, pc>>

Reset ==
    /\ pc = "post"
    /\ CharAt(loop) # Candidate(loop) /\ matchIdx = Sentinel
    /\ bestOffset' = IF CharAt(loop) < Candidate(loop)
                     THEN loop
                     ELSE bestOffset
    /\ fail' = [fail EXCEPT ![loop - bestOffset] = matchIdx]
    /\ pc' = "increment"
    /\ UNCHANGED <<string, slen, matchIdx, loop>>

Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<string, slen, fail, matchIdx, bestOffset>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == LoopCheck \/ Lookup \/ Compare \/ Jump \/ Follow \/ Reset \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopCheck) /\ WF_vars(Lookup)
        /\ WF_vars(Compare) /\ WF_vars(Increment)

Correctness ==
    /\ \A i \in 0 .. (slen - 1) :
         Rot(string)[1 ..] <= Rot(SubSeq(string, i + 1, slen)
                                  \o SubSeq(string, 1, i))
    /\ \A i \in 0 .. (slen - 1) :
         (Rot(string)[1 ..] = Rot(SubSeq(string, i + 1, slen)
                                  \o SubSeq(string, 1, i))) => i >= bestOffset

Termination == <>(pc = "done")

====