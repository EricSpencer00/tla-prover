---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT CharacterSet \* the alphabet, a finite subset of Nat
CONSTANT Nat \* sentinel value, distinct from any character

(*-----------------------------------------------------------------
  Derived sets and definitions
-----------------------------------------------------------------*)
Char == CharacterSet

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    s,          \* input string (a sequence of characters, zero-indexed)
    n,          \* length of the input string
    f,          \* failure function array, indexed 0..2*n
    q,          \* pattern‑match index (current failure function value)
    i,          \* outer loop counter, 1..2*n
    best,       \* best rotation offset, 0..n-1
    pc,         \* program counter (represents labeled steps)
    terminated  \* boolean flag indicating termination

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Sentinel == Nat

ZeroBasedSeq(seq) == [j \in 0..(Len(seq)-1) |-> seq[j]]

(* Indexing into the circular string *)
CharAt(pos) == s[(pos) % n]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ s \in Seq(Char)          \* any zero‑indexed sequence of characters
    /\ n = Len(s)
    /\ f = [j \in 0..(2*n) |-> Sentinel]
    /\ q = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"
    /\ terminated = FALSE

(*-----------------------------------------------------------------
  Actions (labeled steps)
-----------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*n THEN
          /\ pc' = "Lookup"
          /\ UNCHANGED <<s, n, f, q, i, best, terminated>>
       ELSE
          /\ terminated' = TRUE
          /\ pc' = "Terminated"
          /\ UNCHANGED <<s, n, f, q, i, best, terminated>>

Lookup ==
    /\ pc = "Lookup"
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, f, q, i, best, terminated>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF CharAt(i) # CharAt(best + q + 1) /\ q # Sentinel THEN
          /\ q' = f[q]
          /\ pc' = "InnerLoop"
       ELSE IF CharAt(i) < CharAt(best + q + 1) /\ q # Sentinel THEN
          /\ best' = (i - q - 1) % n
          /\ q' = f[q]
          /\ pc' = "InnerLoop"
       ELSE
          /\ pc' = "PostCompare"
    /\ UNCHANGED <<s, n, f, i, terminated>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF CharAt(i) # CharAt(best + q + 1) /\ q = Sentinel THEN
          /\ IF CharAt(i) < CharAt(best) THEN
                /\ best' = i % n
             ELSE
                /\ best' = best
          /\ f' = [f EXCEPT ![best + q + 1] = IF CharAt(i) = CharAt(best) THEN q + 1 ELSE Sentinel]
       ELSE
          /\ f' = [f EXCEPT ![best + q + 1] = IF q = Sentinel THEN 1 ELSE q + 1]
    /\ i' = i + 1
    /\ q' = Sentinel
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<s, n, terminated>>

TerminateStutter ==
    /\ terminated
    /\ pc = "Terminated"
    /\ UNCHANGED <<s, n, f, q, i, best, pc, terminated>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostCompare
    \/ TerminateStutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<s, n, f, q, i, best, pc, terminated>>

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ s \in Seq(Char)
    /\ n = Len(s)
    /\ f \in [0..(2*n) -> (0..(2*n) \cup {Sentinel})]
    /\ q \in (0..(2*n)) \cup {Sentinel}
    /\ i \in 1..(2*n)
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostCompare", "Terminated"}
    /\ terminated \in BOOLEAN

(*-----------------------------------------------------------------
  Correctness invariant (lexicographically least rotation)
-----------------------------------------------------------------*)
RotSeq(off) == <<CharAt(off + j) : j \in 0..(n-1)>>

Correctness ==
    /\ terminated
    /\ \A off \in 0..(n-1) : RotSeq(best) << RotSeq(off)   \* lexicographic order

=============================================================================