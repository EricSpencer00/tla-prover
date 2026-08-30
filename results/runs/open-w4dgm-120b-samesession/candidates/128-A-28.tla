---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The sequence itself is only ever a prefix of the finite model's bound.
\* The operator below replaces Sequences!Seq so it is finite and checkable.
LimitedSeq(f, n) == IF n = 0 THEN <<>> ELSE [f EXCEPT ![n]]

\* The algorithm is essentially a planner: it has one loop, the set of
\* intervals still needing partitioning, and a state-equivalence relation
\* between the current sequence and the original that is the only thing
\* keeping the permutation-argument honest across a nondeterministic
\* partition step.
\* Partition(f, lo, hi, p) is the nondeterministic choice: any rearrangement
\* of f's values on indices lo..hi that respects the pivot p's ordering.
\* The full loop body is in one action so each loop iteration is a single
\* state transition, which is what keeps the per-iteration accounting
\* (the interval set shrinking and the permutation-relation holding) a
\* per-step fact instead of a per-macro-step one.
Partition(f, lo, hi, p) ==
  {g \in LimitedSeq([i \in 1..MaxSeqLen |-> IF i \notin lo..hi THEN f[i]
                                          ELSE IF i <= p THEN f[i]
                                          ELSE f[i + 1]], MaxSeqLen) :
     \A i \in lo..p : g[i] <= g[p]
       /\ \A i \in p+1..hi : g[i] >= g[p]}

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

\* Intervals are contiguous index ranges; 'todo' is the work set.  The loop
\* invariant below is a per-subinterval permutation + sortedness property,
\* so it is a multi-interval fact that is preserved by the single rewrite
\* that the whole action below performs.
TypeOK ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig \in LimitedSeq(Values, MaxSeqLen)
  /\ todo \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"main", "done"}

Init ==
  /\ \E f \in LimitedSeq(Values, MaxSeqLen) :
       /\ seq = f
       /\ orig = f
  /\ todo = {1 \X MaxSeqLen}
  /\ pc = "main"

\* The whole loop body in one atomic step; always available while pc = "main".
Main ==
  /\ pc = "main"
  /\ \E lo, hi \in 1..MaxSeqLen :
       /\ <<lo, hi>> \in todo
       /\ todo' = (todo \ {<<lo, hi>>}) \cup
            IF lo = hi THEN {}
            ELSE
              \E p \in lo..hi :
                {<<lo, p>>, <<p+1, hi>>}
       /\ seq' =
            IF lo = hi THEN seq
            ELSE CHOOSE g \in Partition(seq, lo, hi, lo)
                         : TRUE
  /\ pc' = IF \A lo, hi \in 1..MaxSeqLen : <<lo, hi>> \in todo
            THEN "done" ELSE pc

Done ==
  /\ pc = "done"
  /\ pc' = pc
  /\ UNCHANGED <<seq, orig, todo>>

Next == Main \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Main)

\* A partition never drops or creates a domain value, only reorders.
Permutation(f, g) ==
  \A x \in Values : \E S \in [1..MaxSeqLen -> Values] :
     /\ \A i \in 1..MaxSeqLen : S[i] \in Values
     /\ S \in [1..MaxSeqLen -> g]
     /\ \A i \in 1..MaxSeqLen : f[S[i]] = x

\* The invariant is per-subinterval: each interval left in the work set is
\* already locally sorted and locally a permutation of the original values
\* on that interval.
Inv ==
  /\ \A lo, hi \in 1..MaxSeqLen :
       (<<lo, hi>> \in todo) =>
         /\ Permutation([i \in 1..MaxSeqLen |-> orig[i]],
                        [i \in 1..MaxSeqLen |-> seq[i]])
         /\ \A i \in lo..hi-1 : seq[i] <= seq[i+1]
  /\ (todo = {}) =>
       /\ Permutation([i \in 1..MaxSeqLen |-> orig[i]],
                      [i \in 1..MaxSeqLen |-> seq[i]])
       /\ \A i \in 1..MaxSeqLen-1 : seq[i] <= seq[i+1]

PCorrect == pc = "done" => (todo = {})
TypeOKOK == TypeOK

Termination == <>(pc = "done")

====