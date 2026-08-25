---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

\* ---------- Helper definitions ----------
LimitedSeq(V, n) ==
  { s \in Seq(V) :
      Len(s) <= n /\ Len(s) >= 1 }

Intervals(s) ==
  { <<i, j>> :
      i \in 1..Len(s) /\ j \in i..Len(s) }

SetAddInterval(I) ==
  IF I[1] <= I[2] THEN { I } ELSE {}

IsPermutation(s, t) ==
  \E f \in [1..Len(s) -> 1..Len(s)] :
    (\A i \in 1..Len(s) : t[i] = s[f[i]]) /\
    (\A i, j \in 1..Len(s) : f[i] = f[j] => i = j)

Partition(s, int, p) ==
  { s' \in Seq(Values) :
      Len(s') = Len(s) /\
      \A k \in 1..Len(s) : (k \notin int) => s'[k] = s[k] /\
      \A i \in int[1]..p : \A j \in p+1..int[2] : s'[i] <= s'[j] /\
      IsPermutation(s, s') }

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ---------- Initial predicate ----------
Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ---------- Main step ----------
RunStep ==
  /\ work # {}
  /\ \E int \in work :
       IF int[1] = int[2] THEN
         /\ work' = work \ {int}
         /\ UNCHANGED <<seq, orig, pc>>
       ELSE
         /\ \E p \in int[1]..int[2] :
               \E s' \in Partition(seq, int, p) :
                 /\ seq' = s'
                 /\ orig' = orig
                 /\ pc' = "Run"
                 /\ LET lowInt  == <<int[1], p-1>>
                        highInt == <<p+1, int[2]>>
                    IN
                    work' = (work \ {int})
                           \cup SetAddInterval(lowInt)
                           \cup SetAddInterval(highInt)
         /\ UNCHANGED pc

\* ---------- Termination step ----------
Terminate ==
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* ---------- Stuttering after termination ----------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == RunStep \/ Terminate \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ---------- Invariants ----------
TypeOK ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig \in LimitedSeq(Values, MaxSeqLen)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ TypeOK
  /\ IsPermutation(orig, seq)

PCorrect ==
  /\ pc = "Done"
     => /\ Sorted(seq)
        /\ IsPermutation(orig, seq)

\* ---------- Liveness property ----------
Termination == <> (pc = "Done")
====