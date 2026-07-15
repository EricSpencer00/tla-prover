---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, TLC

(* --constants (to be instantiated by the .cfg) ------------------- *)
CONSTANTS Values, MaxSeqLen, Seq

(* --derived constants -------------------------------------------- *)
\* Domain of indices for the current sequence (1..Len)
Index == 1 .. Len

(* --variables ----------------------------------------------------- *)
VARIABLES seq, orig, work, pc

(* --type definitions ---------------------------------------------- *)
TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq {{i, j} : i, j \in Index : i <= j}
  /\ pc \in {"Loop", "Done"}

(* --initial state ------------------------------------------------- *)
Init ==
  /\ seq = Seq
  /\ orig = seq
  /\ work = {{1, Len}}
  /\ pc = "Loop"

Len == Len(seq)

(* -----------------------------------------------------------------
   Helper definitions
   ----------------------------------------------------------------- *)

Interval(i, j) == {i, j} \in work

Single(i, j) == i = j

(* A partition over interval [i..j] with pivot p (i <= p <= j) produces a
   new sequence seq' that:
   - leaves elements outside [i..j] unchanged,
   - rearranges the elements inside [i..j] so that all elements at positions
     i..p are <= all elements at positions p+1..j.
   The exact arrangement is nondeterministic among all such possibilities. *)
Partition(seq, i, j, p) ==
  { seqp \in Seq :
      /\ \A k \in Index \ (k < i \/ k > j) : seqp[k] = seq[k]
      /\ \A a \in i .. p : \A b \in (p+1) .. j :
            seqp[a] <= seqp[b]
      /\ \A x \in seq[i..j] : \E m \in i .. j : seqp[m] = x }

(* -----------------------------------------------------------------
   Actions
   ----------------------------------------------------------------- *)

Loop ==
  \E i, j \in Index :
    /\ i <= j
    /\ {i, j} \in work
    /\ IF i = j
          THEN
            /\ work' = work \ {{i, j}}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            \E p \in i .. j :
               \E newSeq \in Partition(seq, i, j, p) :
                 /\ seq' = newSeq
                 /\ work' = (work \ {{i, j}}) \cup {{i, p}, {p+1, j}}
                 /\ UNCHANGED <<orig, pc>>

Done ==
  /\ work = {}
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work>>

TerminatingStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ /\ pc = "Loop" /\ Loop /\ pc' = IF work' = {} THEN "Done" ELSE "Loop"
  \/ TerminatingStutter

(* -----------------------------------------------------------------
   Specification
   ----------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(* -----------------------------------------------------------------
   Safety invariant (partial correctness)
   ----------------------------------------------------------------- *)

Sorted ==
  \A i, j \in Index : i < j => seq[i] <= seq[j]

Permutation ==
  \A x \in Values :
    Cardinality({ i \in Index : seq[i] = x }) =
    Cardinality({ i \in Index : orig[i] = x })

PCorrect ==
  /\ pc = "Done"
  /\ Sorted
  /\ Permutation

(* -----------------------------------------------------------------
   Simple type invariant (required by the .cfg)
   ----------------------------------------------------------------- *)

Inv == /\ seq \in Seq
       /\ orig \in Seq
       /\ work \subseteq {{i, j} : i, j \in Index : i <= j}
       /\ pc \in {"Loop", "Done"}

(* -----------------------------------------------------------------
   Liveness property (termination)
   ----------------------------------------------------------------- *)

Termination == []<>(pc = "Done")

====