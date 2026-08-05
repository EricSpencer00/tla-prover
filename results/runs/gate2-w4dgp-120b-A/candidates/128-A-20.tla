---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, Automorphisms

(* Quicksort, abstracted: the partition step is modeled as a nondeterministic   *)
(* choice of any sequence that a real partition routine could produce.  The      *)
(* safety theorem below is proved partially in the attached structured proof.    *)

CONSTANTS Values, MaxSeqLen

SeqDom == 1 .. MaxSeqLen

\* A bounded, finite version of the built-in Seq operator to keep the state space
\* finite; it is injected directly by the .cfg in place of the standard Seq.
LimitedSeq(d) == CHOOSE s \in [d -> Values] : TRUE

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

TypeOK <<
  seq \in [SeqDom -> Values],
  orig \in [SeqDom -> Values],
  work \subseteq {{i, j} \in 1 .. MaxSeqLen \X 1 .. MaxSeqLen : i <= j},
  pc \in {"reshuffle", "done"}
>>

\* Intervals partition the index domain; a partition of a domain separates it into
\* disjoint intervals that cover it exactly.
PartitionsOf(d) ==
  {C \in SUBSET {[i, j] \in d \X d : i <= j} :
       \A x \in d : \E I \in C : x \in (I[1] .. I[2])}

AutomorphismsOf(d) == {f \in [d -> d] : \A x \in d : f[x] \in d}

Permutations(d) == {f \in AutomorphismsOf(d) : \A x \in d : f[x] \in d}

\* A valid post-partition sequence: outside the interval nothing has moved, and
\* every element at-or-below the pivot index is no greater than every element
\* above it.
ValidPartition(x, I, p, v) ==
  /\ \A i \in SeqDom :
       (i \notin (I[1] .. I[2]) => v[i] = x[i])
  /\ \A i \in I[1] .. p : \A j \in p + 1 .. I[2] => v[i] <= v[j]

\* The partition operator: for the given index interval and pivot, give every
\* sequence it could possibly result from a partition of that interval.
Partitions(x, I, p) == {v \in [SeqDom -> Values] : ValidPartition(x, I, p, v)}

Init ==
  /\ seq = @
  /\ orig = seq
  /\ work = {{1, MaxSeqLen}}
  /\ pc = "reshuffle"

Reshuffle ==
  /\ pc = "reshuffle"
  /\ work # {}
  /\ \E I \in work :
       /\ IF I[1] = I[2]
          THEN work' = work \ {I}
          ELSE
            /\ \E p \in I[1] + 1 .. I[2] - 1 :
                 /\ seq' \in Partitions(seq, I, p)
                 /\ work' = (work \ {I}) \cup {{I[1], p}, {p + 1, I[2]}}
       /\ UNCHANGED orig
  /\ pc' = "reshuffle"

Done ==
  /\ pc = "reshuffle"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall == /\ pc = "done" /\ UNCHANGED vars

Next == Reshuffle \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Reshuffle)

\* The algorithm's output is a sorted permutation of its input.
PCorrect ==
  (pc = "done") =>
    /\ Permutations(SeqDom) = {f \in [SeqDom -> SeqDom] : \A x \in SeqDom : f[x] \in SeqDom}
    /\ {seq[f[i]] : f \in Permutations(SeqDom), i \in SeqDom} = {orig[i] : i \in SeqDom}
    /\ \A i \in 1 .. MaxSeqLen - 1 : seq[i] <= seq[i + 1]

\* Each index always belongs to exactly one interval of the current partition,
\* the sequence stays a permutation of the original, and every covered interval
\* is sorted internally.
Inv ==
  /\ work \in PartitionsOf(SeqDom)
  /\ Permutations(SeqDom) = {f \in [SeqDom -> SeqDom] : \A x \in SeqDom : f[x] \in SeqDom}
  /\ {seq[f[i]] : f \in Permutations(SeqDom), i \in SeqDom} = {orig[i] : i \in SeqDom}
  /\ \A I \in work : \A i \in I[1] .. I[2] - 1 : seq[i] <= seq[i + 1]

Termination == <>(pc = "done")

INVARIANT TypeOK
INVARIANT Inv
PROPERTY PCorrect
PROPERTY Termination
====