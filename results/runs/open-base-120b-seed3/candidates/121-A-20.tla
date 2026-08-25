---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Zero‑based indexing for sequences.  We represent a string as a finite
\* sequence (1‑indexed, as provided by the Sequences module) but expose
\* zero‑based access via the helper CharAt.
\* ----------------------------------------------------------------------
CharAt(s, pos) == 
  LET len == Len(s) IN
    IF len = 0 THEN Sentinel
    ELSE s[(pos % len) + 1]

\* Rotation of the string starting at offset off (zero‑based).  The rotation
\* is represented as a function from 0..Len-1 to characters.
\* ----------------------------------------------------------------------
Rotation(s, off) ==
  [j \in 0..(Len(s)-1) |-> CharAt(s, off + j)]

\* Lexicographic ≤ on two rotations (functions from 0..Len-1).  The order on
\* characters is the natural order on the underlying naturals.
\* ----------------------------------------------------------------------
LexLe(r1, r2) ==
  \E i \in 0..(Len(r1)) :
    ( /\ \A j \in 0..(i-1) : r1[j] = r2[j]
       /\ ( i = Len(r1) \/ r1[i] <= r2[i] ) )

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Str, Len, Fail, P, I, Best, PC

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Str \in Seq(CharacterSet)                \* input string (zero‑based logical)
  /\ Len = Len(Str)
  /\ Fail = [j \in 0..(2*Len) |-> Sentinel]   \* failure function, undefined entries are Sentinel
  /\ P = Sentinel
  /\ I = 1                                      \* outer loop counter starts at 1
  /\ Best = 0                                   \* best rotation offset
  /\ PC = "OuterCheck"                          \* start at outer‑loop test

\* ----------------------------------------------------------------------
\* Actions for each program‑counter label
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ PC = "OuterCheck"
  /\ IF I < 2*Len
       THEN /\ PC' = "Lookup"
            /\ UNCHANGED <<Str, Len, Fail, P, I, Best>>
       ELSE /\ PC' = "Done"
            /\ UNCHANGED <<Str, Len, Fail, P, I, Best>>

Lookup ==
  /\ PC = "Lookup"
  /\ let idx == (Best + I) % Len in
        /\ P' = Fail[idx]
        /\ PC' = "Compare"
        /\ UNCHANGED <<Str, Len, Fail, I, Best>>

Compare ==
  /\ PC = "Compare"
  /\ LET a == CharAt(Str, Best + I)
        b == IF P = Sentinel THEN Sentinel ELSE CharAt(Str, Best + P) IN
     /\ IF a = b
          THEN 
               /\ IF P = Sentinel
                     THEN PC' = "PostCompare"
                     ELSE /\ P' = Fail[(Best + P) % Len]   \* follow failure link
                          /\ PC' = "Compare"
               /\ UNCHANGED <<Str, Len, Fail, I, Best>>
          ELSE 
               /\ IF a < b
                     THEN /\ Best' = (Best + I) % Len
                          /\ UNCHANGED <<Str, Len, Fail, I, P>>
                     ELSE /\ UNCHANGED <<Str, Len, Fail, I, P, Best>>
               /\ PC' = "PostCompare"

PostCompare ==
  /\ PC = "PostCompare"
  /\ LET a == CharAt(Str, Best + I)
        b == IF P = Sentinel THEN Sentinel ELSE CharAt(Str, Best + P) IN
     /\ IF a # b /\ P = Sentinel
          THEN 
               /\ IF a < b
                    THEN Best' = (Best + I) % Len
                    ELSE UNCHANGED Best
               /\ Fail' = [Fail EXCEPT ![(Best + I) % Len] = IF P = Sentinel THEN Sentinel ELSE 1 + P]
          ELSE 
               /\ UNCHANGED <<Best, Fail>>
     /\ PC' = "Inc"
     /\ UNCHANGED <<Str, Len, I, P>>

Inc ==
  /\ PC = "Inc"
  /\ I' = I + 1
  /\ PC' = "OuterCheck"
  /\ UNCHANGED <<Str, Len, Fail, P, Best>>

Done ==
  /\ PC = "Done"
  /\ UNCHANGED <<Str, Len, Fail, P, I, Best>>

\* Stuttering step to allow the model to stay in the final state
Stutter ==
  /\ PC = "Done"
  /\ UNCHANGED <<Str, Len, Fail, P, I, Best, PC>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ PostCompare
  \/ Inc
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Str, Len, Fail, P, I, Best, PC>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ Str \in Seq(CharacterSet)
  /\ Len = Len(Str)
  /\ Fail \in [0..(2*Len) -> (0..Len) \cup {Sentinel}]
  /\ P \in (0..Len) \cup {Sentinel}
  /\ I \in Nat
  /\ Best \in 0..(Len-1)    \* valid rotation offset
  /\ PC \in {"OuterCheck", "Lookup", "Compare", "PostCompare", "Inc", "Done"}

\* ----------------------------------------------------------------------
\* Correctness: Best identifies the lexicographically minimal rotation
\* ----------------------------------------------------------------------
Correctness ==
  /\ Len = 0
     => Best = 0
  /\ Len > 0
     => \A off \in 0..(Len-1) :
          LexLe(Rotation(Str, Best), Rotation(Str, off))

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeInvariant, Correctness

\* ----------------------------------------------------------------------
\* Finite version of Nat required by the .cfg (replaces Nat in ZSequences)
\* ----------------------------------------------------------------------
[ZSequences]CharacterSet == CharacterSet

====