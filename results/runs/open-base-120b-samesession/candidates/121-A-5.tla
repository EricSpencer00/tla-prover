---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\*--------------------------------------------------------------------
\* Constants
\********************************************************************
CONSTANT CharacterSet               \* finite subset of Nat, supplied by the model

\*--------------------------------------------------------------------
\* Sentinels and helper definitions
\********************************************************************
Sentinel == -1

\* Zero‑indexed string: a function from 0..len-1 to characters
String == [pos \in Nat -> CharacterSet]

\* Failure function: maps indices 0..2*len to either a valid index or Sentinel
FailFun(len) == [idx \in 0..(2*len) -> Nat \cup {Sentinel}]

\* Rotation of the string starting at offset off (0‑based)
Rot(off, s, l) ==
  [j \in 1..l |-> s[(off + (j-1)) % l]]

\* Lexicographic ordering on rotations (using the sequence ordering from Sequences)
LexLeq(off1, off2, s, l) ==
  SeqLex(Rot(off1, s, l), Rot(off2, s, l))

\*--------------------------------------------------------------------
\* Variables
\********************************************************************
VARIABLES str, len, fail, p, i, best, pc

vars == << str, len, fail, p, i, best, pc >>

\*--------------------------------------------------------------------
\* Initial state
\********************************************************************
Init ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = FailFun(len) \* all entries are Sentinel initially
  /\ \A idx \in DOMAIN fail : fail[idx] = Sentinel
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* Actions (one for each labeled step)
\********************************************************************

\* 1. Outer loop check
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*len
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED << str, len, fail, p, i, best >>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << str, len, fail, p, i, best >>

\* 2. Failure function lookup (relative to current best)
Lookup ==
  /\ pc = "Lookup"
  /\ let idx == (i - best) % (2*len + 1) in
        p' = fail[idx]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED << str, len, fail, i, best >>

\* 3. Inner comparison loop (abstracted)
InnerLoop ==
  /\ pc = "InnerLoop"
  /\ let curPos == i % len
         candPos == (best + p) % len \* candidate position based on p
         curChar == str[curPos]
         candChar == str[candPos]
     in
        IF curChar = candChar
           THEN /\ p' = p
                /\ pc' = "InnerLoop"   \* stay in inner loop (real algorithm would advance)
                /\ UNCHANGED << str, len, fail, i, best >>
        ELSE IF p # Sentinel
                THEN /\ p' = fail[(i - best) % (2*len + 1)]   \* follow failure chain
                     /\ pc' = "InnerLoop"
                     /\ UNCHANGED << str, len, fail, i, best >>
        ELSE /\ pc' = "PostComp"
           /\ UNCHANGED << str, len, fail, i, best, p >>

\* 4. Update best if current char is smaller (used in inner loop when appropriate)
UpdateBestInner ==
  /\ pc = "InnerLoop"
  /\ let curPos == i % len
         candPos == (best + p) % len
         curChar == str[curPos]
         candChar == str[candPos]
     in curChar < candChar
  /\ best' = curPos
  /\ pc' = "InnerLoop"
  /\ UNCHANGED << str, len, fail, i, p >>

\* 5. Post‑comparison handling
PostComp ==
  /\ pc = "PostComp"
  /\ let curPos == i % len
         candPos == (best) % len
         curChar == str[curPos]
         candChar == str[candPos]
     in 
        IF curChar # candChar /\ p = Sentinel
           THEN /\ IF curChar < candChar THEN best' = curPos ELSE best' = best
                /\ fail' = [fail EXCEPT ![(i - best) % (2*len + 1)] = IF curChar < candChar THEN Sentinel ELSE p + 1]
                /\ pc' = "Inc"
           ELSE /\ fail' = [fail EXCEPT ![(i - best) % (2*len + 1)] = IF p = Sentinel THEN Sentinel ELSE p + 1]
                /\ best' = best
                /\ pc' = "Inc"
  /\ UNCHANGED << str, len, i, p >>

\* 6. Increment outer loop counter
Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, len, fail, p, best >>

\* 7. Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

\*--------------------------------------------------------------------
\* Next-state relation
\********************************************************************
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBestInner
  \/ PostComp
  \/ Inc
  \/ Stutter

\*--------------------------------------------------------------------
\* Type invariant
\********************************************************************
TypeInvariant ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = FailFun(len)
  /\ \A idx \in DOMAIN fail : fail[idx] \in Nat \cup {Sentinel}
  /\ p \in Nat \cup {Sentinel}
  /\ i \in Nat
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

\*--------------------------------------------------------------------
\* Correctness invariant (holds when algorithm terminates)
\********************************************************************
Correctness ==
  (pc = "Done") =>
    \A k \in 0..len-1 : LexLeq(best, k, str, len)

\*--------------------------------------------------------------------
\* Specification
\********************************************************************
Spec == Init /\ [][Next]_vars

====