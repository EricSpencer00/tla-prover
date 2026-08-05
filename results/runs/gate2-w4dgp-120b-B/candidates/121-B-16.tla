---- MODULE LeastCircularSubstring ----
EXTENDS Integers, ZSequences

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

Corpus == ZSeq(CharacterSet)
nil == -1

VariableState == [b: Corpus, n: Nat, f: [0..2*ZLen(Corpus) -> 0..2*ZLen(Corpus) \cup {nil}],
                   i: (0..2*ZLen(Corpus)) \cup {nil}, j: (0..2*ZLen(Corpus)) \cup {1},
                   k: ZIndices(Corpus) \cup {0}, pc: {"L3","L5","L6","L7","L8","L9","L10","L11","L12","L13","L14","LVR","Done"}]

vars == << VariableState.b, VariableState.n, VariableState.f,
          VariableState.i, VariableState.j, VariableState.k, VariableState.pc >>

Init == VariableState \in [b: Corpus, n: Nat,
  f: [0..2*ZLen(Corpus) -> 0..2*ZLen(Corpus) \cup {nil}],
  i: (0..2*ZLen(Corpus)) \cup {nil}, j: (0..2*ZLen(Corpus)) \cup {1},
  k: ZIndices(Corpus) \cup {0}, pc: {"L3","L5","L6","L7","L8","L9","L10","L11","L12","L13","L14","LVR","Done"}] /\

         /\ VariableState.b \in Corpus
         /\ VariableState.n = ZLen(VariableState.b)
         /\ VariableState.f = [index \in 0..2*ZLen(VariableState.b) |-> nil]
         /\ VariableState.i = nil
         /\ VariableState.j = 1
         /\ VariableState.k = 0
         /\ VariableState.pc = "L3"

L3 == /\ VariableState.pc = "L3"
      /\ IF VariableState.j < 2 * VariableState.n
            THEN /\ VariableState' = [VariableState EXCEPT !.pc = "L5"]
            ELSE /\ VariableState' = [VariableState EXCEPT !.pc = "Done"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.i, VariableState.j, VariableState.k >>

L5 == /\ VariableState.pc = "L5"
      /\ VariableState' = [VariableState EXCEPT !.i = VariableState.f[VariableState.j - VariableState.k - 1],
                                             !.pc = "L6"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.j, VariableState.k >>

L6 == /\ VariableState.pc = "L6"
      /\ IF VariableState.b[VariableState.j % VariableState.n] /= VariableState.b[(VariableState.k + VariableState.i + 1) % VariableState.n] /\ VariableState.i # nil
            THEN /\ VariableState' = [VariableState EXCEPT !.pc = "L7"]
            ELSE /\ VariableState' = [VariableState EXCEPT !.pc = "L10"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.i, VariableState.j, VariableState.k >>

L7 == /\ VariableState.pc = "L7"
      /\ IF VariableState.b[VariableState.j % VariableState.n] < VariableState.b[(VariableState.k + VariableState.i + 1) % VariableState.n]
            THEN /\ VariableState' = [VariableState EXCEPT !.pc = "L8"]
            ELSE /\ VariableState' = [VariableState EXCEPT !.pc = "L9"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.i, VariableState.j, VariableState.k >>

L8 == /\ VariableState.pc = "L8"
      /\ VariableState' = [VariableState EXCEPT !.k = VariableState.j - VariableState.i - 1,
                                             !.pc = "L9"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.i, VariableState.j >>

L9 == /\ VariableState.pc = "L9"
      /\ VariableState' = [VariableState EXCEPT !.i = VariableState.f[VariableState.i],
                                             !.pc = "L6"]
      /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.j, VariableState.k >>

L10 == /\ VariableState.pc = "L10"
       /\ IF VariableState.b[VariableState.j % VariableState.n] /= VariableState.b[(VariableState.k + VariableState.i + 1) % VariableState.n] /\ VariableState.i = nil
             THEN /\ VariableState' = [VariableState EXCEPT !.pc = "L11"]
             ELSE /\ VariableState' = [VariableState EXCEPT !.pc = "L14"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                       VariableState.i, VariableState.j, VariableState.k >>

L11 == /\ VariableState.pc = "L11"
       /\ IF VariableState.b[VariableState.j % VariableState.n] < VariableState.b[(VariableState.k + VariableState.i + 1) % VariableState.n]
             THEN /\ VariableState' = [VariableState EXCEPT !.pc = "L12"]
             ELSE /\ VariableState' = [VariableState EXCEPT !.pc = "L13"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                       VariableState.i, VariableState.j, VariableState.k >>

L12 == /\ VariableState.pc = "L12"
       /\ VariableState' = [VariableState EXCEPT !.k = VariableState.j,
                                             !.pc = "L13"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                       VariableState.i, VariableState.j >>

L13 == /\ VariableState.pc = "L13"
       /\ VariableState' = [VariableState EXCEPT !.f = [VariableState.f EXCEPT ![VariableState.j - VariableState.k] = nil],
                                             !.pc = "LVR"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.i,
                       VariableState.j, VariableState.k >>

L14 == /\ VariableState.pc = "L14"
       /\ VariableState' = [VariableState EXCEPT !.f = [VariableState.f EXCEPT ![VariableState.j - VariableState.k] = VariableState.i + 1],
                                             !.pc = "LVR"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.i,
                       VariableState.j, VariableState.k >>

LVR == /\ VariableState.pc = "LVR"
       /\ VariableState' = [VariableState EXCEPT !.j = VariableState.j + 1,
                                             !.pc = "L3"]
       /\ UNCHANGED << VariableState.b, VariableState.n, VariableState.f,
                      VariableState.i, VariableState.k >>

Terminating == VariableState.pc = "Done" /\ UNCHANGED vars

Next == L3 \/ L5 \/ L6 \/ L7 \/ L8 \/ L9 \/ L10 \/ L11 \/ L12 \/ L13 \/ L14 \/ LVR \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(VariableState.pc = "Done")

TypeInvariant ==
  /\ VariableState.b \in Corpus
  /\ VariableState.n = ZLen(VariableState.b)
  /\ VariableState.f \in [0..2*ZLen(Corpus) -> 0..2*ZLen(Corpus) \cup {nil}]
  /\ VariableState.i \in (0..2*ZLen(Corpus)) \cup {nil}
  /\ VariableState.j \in (0..2*ZLen(Corpus)) \cup {1}
  /\ VariableState.k \in ZIndices(Corpus) \cup {0}
  /\ VariableState.pc \in {"L3","L5","L6","L7","L8","L9","L10","L11","L12","L13","L14","LVR","Done"}

IsLeastMinimalRotation(s, r) ==
  LET rotation == Rotation(s, r) IN
  /\ \A other \in Rotations(s) :
       /\ rotation \preceq other.seq
       /\ (rotation = other.seq => r <= other.shift)

Correctness ==
  VariableState.pc = "Done" => IsLeastMinimalRotation(VariableState.b, VariableState.k)

====