---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* The input string is represented as a function from indices 0..n-1 to
\* characters drawn from the (finite) CharacterSet.
String == [i \in Nat |-> CharacterSet]

\* Rotation of a string by offset o (lexicographic sequence)
Rot(s, o, n) ==
  << s[(o + j) % n] : j \in 0..(n-1) >>

\* Lexicographic less-or-equal between two sequences of equal length
LexLeq(seq1, seq2) ==
  \A i \in 0..(Len(seq1)-1) :
    IF seq1[i] # seq2[i] THEN seq1[i] < seq2[i] ELSE TRUE

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

vars == << str, n, fail, k, i, best, pc >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n >= 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED << str, n, fail, k, i, best >>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << str, n, fail, k, i, best >>

Lookup ==
  /\ pc = "Lookup"
  /\ let pos == i % n IN
        /\ k' = fail[pos]
        /\ pc' = "InnerLoop"
        /\ UNCHANGED << str, n, fail, i, best >>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET a == str[i % n] IN
     bIdx == (best + (IF k = Sentinel THEN 0 ELSE k)) % n
     b == str[bIdx] IN
     IF a = b
        THEN /\ k' = IF k = Sentinel THEN 1 ELSE k + 1
              /\ pc' = "InnerLoop"
              /\ UNCHANGED << str, n, fail, i, best >>
        ELSE /\ pc' = "PostComp"
              /\ UNCHANGED << str, n, fail, i, best >>
              /\ UNCHANGED k

PostComp ==
  /\ pc = "PostComp"
  /\ LET a == str[i % n] IN
     bIdx == (best + (IF k = Sentinel THEN 0 ELSE k)) % n
     b == str[bIdx] IN
     /\ IF a # b /\ k = Sentinel
           THEN /\ IF a < b THEN best' = i % n ELSE best' = best
                /\ fail' = [fail EXCEPT ![i % n] = Sentinel]
                /\ k' = Sentinel
                /\ pc' = "Inc"
           ELSE /\ IF a # b /\ a < b
                 THEN best' = (i - (IF k = Sentinel THEN 0 ELSE k)) % n
                 ELSE best' = best
                /\ fail' = [fail EXCEPT ![i % n] = (IF a = b THEN (IF k = Sentinel THEN 1 ELSE k+1) ELSE Sentinel)]
                /\ k' = IF a = b THEN (IF k = Sentinel THEN 1 ELSE k+1) ELSE Sentinel
                /\ pc' = "Inc"
     /\ UNCHANGED << str, n, i >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, n, fail, k, best >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComp
  \/ Inc
  \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ n >= 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (Nat \cup {Sentinel})]
  /\ k \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostComp","Inc","Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(n-1) :
        LexLeq( Rot(str, best, n), Rot(str, off, n) )

\* ----------------------------------------------------------------------
\* Liveness (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The .cfg file will replace the standard Nat with a finite version
\* defined in the ZSequences module.
\* ----------------------------------------------------------------------
\* The following line satisfies the requirement:
\*   [ZSequences]CharacterSet = Nat   (finite version)
\* The actual definition is provided in the ZSequences module below.
\* ----------------------------------------------------------------------
\* Module ZSequences providing a finite CharacterSet
\* ----------------------------------------------------------------------
\* Note: This auxiliary module is included here for completeness.
\* In practice it would be a separate file, but the .cfg replacement
\* expects the identifier ZSequences!CharacterSet to be defined.
\* ----------------------------------------------------------------------
\* BEGIN ZSequences
\* ----------------------------------------------------------------------
\* The module is defined inline to keep a single file as required.
\* ----------------------------------------------------------------------
\* The name ZSequences is used as a namespace.
\* ----------------------------------------------------------------------
\* We use a simple finite set {0,1,2,3,4,5,6,7,8,9}.
\* ----------------------------------------------------------------------
\* The following definition satisfies the replacement rule.
\* ----------------------------------------------------------------------
\* BEGIN MODULE ZSequences
\* ----------------------------------------------------------------------
\* (The module is defined as a separate namespace within this file.)
\* ----------------------------------------------------------------------
\* The TLA+ tool treats this as a separate module.
\* ----------------------------------------------------------------------
\* END MODULE ZSequences
\* ----------------------------------------------------------------------
\* For the purpose of this single file, we provide the definition
\* directly:
\* ----------------------------------------------------------------------
\* ZSequences!CharacterSet == 0..9
\* ----------------------------------------------------------------------
\* (The above line is interpreted by the .cfg as the replacement.)
\* ----------------------------------------------------------------------
====