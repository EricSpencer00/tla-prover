---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets

(* Adaptive bounded model of the lexicographically-least circular substring   *)
(* algorithm from Booth (1980), using a failure function like KMP's and a      *)
(* doubled scan.  The spec must expose exactly the identifiers the reference   *)
(* model-checker configuration expects.                                        *)

CONSTANTS
    CharacterSet

Zero == 0
Sentinel == -1

VARIABLES
    input,          \* the circular string, chosen nondeterministically from the corpus
    length,         \* length of the input string
    failure,        \* failure function for pattern matches, indexed over the doubled scan
    index,          \* pattern-match index (failure-function lookup)
    loop,           \* outer loop counter, runs up to twice the string length
    best,           \* the best rotation offset found so far
    pc              \* program counter: which labeled step is executing

vars == << input, length, failure, index, loop, best, pc >>

LessThan(a, b) == a < b

Rot(s, k) == LET n == Len(s) IN
                 [i \in 0..(n-1) |-> s[((k + i) % n)]]

\* The corpus: every zero-indexed sequence over the character set up to the
\* maximum length set by the model-checking module.
Corpus == UNION { [1..n -> CharacterSet] : n \in 0..4 }

TypeInvariant ==
    /\ input \in Corpus
    /\ length = Len(input)
    /\ failure \in [0..(2*length) -> {Sentinel} \cup (0..(2*length))]
    /\ index \in {Sentinel} \cup (0..(2*length))
    /\ loop \in 1..(2*length)
    /\ best \in 0..(length - 1)
    /\ pc \in {"outer", "lookup", "inner", "updateBest", "followFail", "post", "increment", "done"}

Init ==
    /\ input' = input
    /\ length' = Len(input)
    /\ failure' = [i \in 0..(2*length) |-> Sentinel]
    /\ index' = Sentinel
    /\ loop' = 1
    /\ best' = 0
    /\ pc' = "outer"

Outer ==
    /\ pc = "outer"
    /\ /\ loop < (2 * length)  /\ pc' = "lookup"
       \/ /\ loop >= (2 * length) /\ pc' = "done"
    /\ UNCHANGED << input, length, failure, index, loop, best >>

Lookup ==
    /\ pc = "lookup"
    /\ index' = IF failure[(loop - 1) % (2 * length)] = Sentinel
                  THEN Sentinel
                  ELSE failure[(loop - 1) % (2 * length)]
    /\ pc' = "inner"
    /\ UNCHANGED << input, length, failure, loop, best >>

Inner ==
    /\ pc = "inner"
    /\ \/ /\ input[(loop % length)] # input[(best + loop) % length] /\ index # Sentinel /\ pc' = "inner"
       \/ /\ (input[(loop % length)] # input[(best + loop) % length] /\ index = Sentinel) \/ (input[(loop % length)] = input[(best + loop) % length])
           /\ pc' = "post"
    /\ UNCHANGED << input, length, failure, index, loop, best >>

UpdateBest ==
    /\ pc = "post"
    /\ input[(loop % length)] # input[(best + loop) % length]
    /\ index = Sentinel
    /\ LessThan(input[(loop % length)], input[(best + loop) % length])
    /\ best' = loop % length
    /\ pc' = "followFail"
    /\ UNCHANGED << input, length, failure, index, loop >>

FollowFail ==
    /\ pc = "post"
    /\ input[(loop % length)] # input[(best + loop) % length]
    /\ index = Sentinel
    /\ ~LessThan(input[(loop % length)], input[(best + loop) % length])
    /\ failure' = [failure EXCEPT ![loop] = Sentinel]
    /\ pc' = "increment"
    /\ UNCHANGED << input, length, index, loop, best >>

Post ==
    /\ pc = "post"
    /\ input[(loop % length)] = input[(best + loop) % length]
    /\ failure' = [failure EXCEPT ![loop] = IF index = Sentinel THEN Sentinel ELSE (index + 1)]
    /\ pc' = "increment"
    /\ UNCHANGED << input, length, index, loop, best >>

Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED << input, length, failure, index, best >>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Outer
    \/ Lookup
    \/ Inner
    \/ UpdateBest
    \/ FollowFail
    \/ Post
    \/ Increment
    \/ Done

Spec == Init /\ [][Next]_vars

\* Correctness: the rotation at 'best' is lexicographically no greater than any
\* other rotation of the input string, and if equal it is the smallest shift.
Correctness ==
    /\ \A k \in 0..(length - 1) : Rot(input, best) <= Rot(input, k)
    /\ \A k \in 0..(length - 1) : Rot(input, best) = Rot(input, k) => best <= k

Termination == <>(pc = "done")

====