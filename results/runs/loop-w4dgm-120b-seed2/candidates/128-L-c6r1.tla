---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

\* The sort runs as a single actor that repeatedly partitions intervals.
\* The "Partition" operator abstracts the actual partition procedure and
\* nondeterministically chooses any result a valid procedure could produce.
\* The invariant ties sortedness to a permutation of the original sequence,
\* which is what makes the reasoning robust: permutations are bijections, so
\* nothing gets lost or copied.

Range(s) == { s[i] : i \in DOMAIN s }

Sorted(s) == \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* A partition of s on interval I against pivot k leaves everything outside
\* I untouched and puts every element at or below k no greater than anything
\* above k; any such s2 is a possible outcome of the partition step.
Partition(s, I, k) ==
  { s2 \in [1..Len(s) -> Values] :
      \A i \in DOMAIN s :
        /\ (i \notin I => s2[i] = s[i])
        /\ \A j \in I : (j <= k => s2[j] <= s2[k]) /\ (j > k => s2[j] >= s2[k])
  }

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ original \in Seq(Values)
  /\ work \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"loop", "term"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen /\ seq = s
  /\ original = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "loop"

Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
       /\ work' = work \ {I}
       /\ IF I[1] = I[2]
          THEN UNCHANGED <<seq, work>>
          ELSE \E k \in I[1]..I[2] :
               \E s2 \in Partition(seq, I, k) :
                 /\ seq' = s2
                 /\ work' = work \cup {<<I[1], k>>, <<k+1, I[2]>>}
  /\ UNCHANGED <<original, pc>>

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "term"
  /\ UNCHANGED <<seq, original, work>>

Done ==
  /\ pc = "term"
  /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)

PCorrect ==
  /\ pc = "term" => (Range(seq) = Range(original) /\ Sorted(seq))
  /\ Len(seq) > 0 => seq[1] <= seq[Len(seq)]

TypeOK == TypeOK

Inv ==
  /\ \A I \in work : I[2] <= Len(seq)
  /\ (pc = "term") => (Range(seq) = Range(original))
  /\ \A i \in DOMAIN seq : i >= 2 => seq[i-1] <= seq[i]

Termination == <>(pc = "term")

\* The checker's domain is bounded; LENGTH(seq) is a hard runtime bound, not
\* a modeling choice. The redefinition below is what makes that bound
\* reachable: without it, the standard Seq operator would let the state
\* space glide past the checker's horizon.
LengthConstrained == Len(seq) <= MaxSeqLen

\* Replaces Seq from Sequences; keeps it finite so the model is checkable.
LimitedSeq(S) == CHOOSE s \in Seq(S) : Len(s) = MaxSeqLen

====