---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

(*--- Replacement for Seq, used by the .cfg ---*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen /\ Len(s) > 0 }

VARIABLES seq, orig, work, pc

(*--- Helper definitions ---*)
(* Domain of a sequence is given by the built‑in operator DOMAIN; no need to redefine it. *)

Intervals == { I \in [low : Nat, high : Nat] :
                I.low <= I.high /\ I.high <= Len(seq) }

CountIn(s, v) == Cardinality({ i \in DOMAIN(s) : s[i] = v })

Permutation(s1, s2) == \A v \in Values : CountIn(s1, v) = CountIn(s2, v)

Sorted(s) == \A i, j \in DOMAIN(s) : i < j => s[i] <= s[j]

Partition(old, new, I, p) ==
  /\ \A j \in DOMAIN(old) \ (I.low .. I.high) : new[j] = old[j]
  /\ \A i \in I.low .. p : \A j \in p+1 .. I.high : new[i] <= new[j]
  /\ \A v \in Values :
        Cardinality({ i \in I.low .. I.high : old[i] = v }) =
        Cardinality({ i \in I.low .. I.high : new[i] = v })

Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Run"

Next ==
  \/ /\ pc = "Run"
     /\ work # {}
     /\ \E I \in work :
          IF I.low = I.high THEN
            /\ work' = work \ { I }
            /\ UNCHANGED <<seq, orig>>
          ELSE
            /\ \E p \in I.low .. I.high :
                 /\ \E newSeq \in Seq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ Partition(seq, newSeq, I, p)
                      /\ seq' = newSeq
                      /\ work' = (work \ { I }) \cup
                         (IF p > I.low THEN { [low |-> I.low, high |-> p-1] } ELSE {}) \cup
                         (IF p < I.high THEN { [low |-> p+1, high |-> I.high] } ELSE {})
                      /\ UNCHANGED orig
  \/ /\ pc = "Run"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

TypeOK ==
  /\ Values \subseteq Int
  /\ MaxSeqLen \in Nat
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ work \subseteq Intervals
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ Permutation(seq, orig)
  /\ \A I \in work : I.low <= I.high /\ I.high <= Len(seq)

Termination == <> (pc = "Done")

====