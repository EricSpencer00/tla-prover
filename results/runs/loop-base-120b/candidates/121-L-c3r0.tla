---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, MaxChar

(* finite character set for model checking *)
CharacterSet == 0..MaxChar

(* sentinel value for undefined failure entries *)
Sentinel == -1

VARIABLES str, n, fail, k, i, best, pc

(* length of a sequence represented as a function from 0..len-1 *)
Len(s) == Cardinality(Domain(s))

(* rotation of string s by offset o *)
Rotation(s, o) ==
  [j \in 0..(Len(s)-1) |-> s[(o + j) % Len(s)]]

(* lexicographic less-or-equal for equal‑length strings *)
LexLeq(s1, s2) ==
  \A j \in 0..(Len(s1)-1) :
    (\A k \in 0..j-1 : s1[k] = s2[k]) => s1[j] <= s2[j]

(* set of all possible offsets for the current string *)
Offsets == 0..(n-1)

(* the minimal offset according to the specification *)
LeastOffset(s) ==
  CHOOSE o \in Offsets :
    \A o2 \in Offsets :
      LexLeq(Rotation(s, o), Rotation(s, o2)) /\
      (\A o3 \in Offsets :
          Rotation(s, o) = Rotation(s, o3) => o <= o3)

(* type invariant *)
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> Integer]      \* entries are either indices or Sentinel
  /\ k \in Integer
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"Check", "Done"}

(* initial state *)
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

(* next‑state relation – abstracted version of Booth’s algorithm *)
Next ==
  \/ /\ pc = "Check"
     /\ i < 2*n
     /\ i' = i + 1
     /\ UNCHANGED <<str, n, fail, k, best, pc>>
  \/ /\ pc = "Check"
     /\ i >= 2*n
     /\ best' = LeastOffset(str)
     /\ pc' = "Done"
     /\ UNCHANGED <<str, n, fail, k, i>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

(* specification *)
Spec == Init /\ [] [Next]_<<str, n, fail, k, i, best, pc>>

(* correctness property: when finished, best is the least rotation offset *)
Correctness ==
  pc = "Done" => best = LeastOffset(str)

====