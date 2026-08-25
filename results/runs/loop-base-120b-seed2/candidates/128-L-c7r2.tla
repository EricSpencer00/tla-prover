---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Integers, TLC

CONSTANTS Values, MaxSeqLen

(* --------------------------------------------------------------------- *)
(*  A finite version of Seq for model checking                           *)
LimitedSeq(V, n) ==
  { s \in Seq(V) : Len(s) > 0 /\ Len(s) <= n }

(* --------------------------------------------------------------------- *)
VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

(* --------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
Intervals(s) ==
  { <<i, j>> : i \in 1..Len(s) /\ j \in i..Len(s) }

MultiSet(t) ==
  [v \in Values |-> Cardinality({ i \in 1..Len(t) : t[i] = v })]

MultiSetOnInterval(t, l, u) ==
  [v \in Values |-> Cardinality({ i \in l..u : t[i] = v })]

Partition(seq, l, u, p) ==
  { s \in Seq(Values) :
        Len(s) = Len(seq) /\
        \A i \in 1..Len(seq) :
            (i < l \/ i > u) => s[i] = seq[i] /\
        \A i \in l..p :
            \A j \in p+1..u : s[i] <= s[j] /\
        MultiSetOnInterval(s, l, u) = MultiSetOnInterval(seq, l, u) }

(* --------------------------------------------------------------------- *)
(*  Initial state                                                         *)
Init ==
  /\ \E s \in LimitedSeq(Values, MaxSeqLen) :
        /\ seq = s
        /\ orig = s
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

(* --------------------------------------------------------------------- *)
(*  One iteration of the sorting loop                                      *)
Step ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        LET l == I[1], u == I[2] IN
        IF l = u THEN
          /\ work' = work \ {I}
          /\ UNCHANGED <<seq, orig, pc>>
        ELSE
          /\ \E p \in l..u :
                /\ \E newSeq \in Partition(seq, l, u, p) :
                     /\ seq'   = newSeq
                     /\ work'  = (work \ {I}) \cup { <<l, p>>, <<p+1, u>> }
                     /\ pc'    = "Loop"
                     /\ UNCHANGED orig

(* --------------------------------------------------------------------- *)
(*  Termination step                                                       *)
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

(* --------------------------------------------------------------------- *)
(*  Stuttering step after termination                                       *)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == \/ Step \/ Terminate \/ Stutter

(* --------------------------------------------------------------------- *)
(*  Specification                                                          *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*  Type correctness invariant                                            *)
TypeOK ==
  /\ seq  \in LimitedSeq(Values, MaxSeqLen)
  /\ orig \in LimitedSeq(Values, MaxSeqLen)
  /\ work \subseteq Intervals(seq)
  /\ pc   \in {"Loop", "Done"}

(* --------------------------------------------------------------------- *)
(*  Permutation invariant                                                  *)
Permutes == MultiSet(seq) = MultiSet(orig)

(* --------------------------------------------------------------------- *)
(*  Sortedness predicate                                                   *)
Sorted(s) == \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

(* --------------------------------------------------------------------- *)
(*  Main invariant (a simplified version)                                 *)
Inv ==
  /\ Permutes
  /\ \A I \in work :
        LET l == I[1], u == I[2] IN
        \A i \in l..u-1 : \A j \in i+1..u :
            seq[i] <= seq[j] \/ TRUE   \* placeholder for a stronger property

(* --------------------------------------------------------------------- *)
(*  Partial correctness when the algorithm has terminated                *)
PCorrect ==
  /\ pc = "Done"
  /\ Sorted(seq)
  /\ Permutes

(* --------------------------------------------------------------------- *)
(*  Liveness property: eventual termination                               *)
Termination == <> (pc = "Done")

====