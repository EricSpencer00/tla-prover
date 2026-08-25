---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The three distinct values that can appear in sequences
Values == { A, B, C }

\* A finite version of Seq, limited by the constant \*bound\*
BoundedSeq(S) ==
  (* the empty sequence *)
  {} 
  \cup
  (* non‑empty sequences whose length does not exceed |bound| *)
  { s \in [1 .. bound -> S] :
        \E n \in 1 .. bound :
          /\ DOMAIN s = 1 .. n }

\* State variables (inherited from the main majority‑vote spec) *)
VARIABLES seq, i, cand, cnt

\* Length of a (possibly empty) sequence *)
SeqLen(s) == IF DOMAIN s = {} THEN 0 ELSE Cardinality(DOMAIN s)

\* Initial state *)
Init ==
  /\ seq \in BoundedSeq(Values)
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

\* One step of the Boyer‑Moore scan *)
Next ==
  LET len == SeqLen(seq) IN
  /\ i <= len
  /\ LET x == seq[i] IN
       IF cnt = 0 THEN
         /\ cand' = x
         /\ cnt' = 1
       ELSE IF x = cand THEN
         /\ cand' = cand
         /\ cnt' = cnt + 1
       ELSE
         /\ cand' = cand
         /\ cnt' = cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

\* Stutter after the scan is finished (deadlock checking is disabled) *)
NextStutter ==
  LET len == SeqLen(seq) IN
  /\ i > len
  /\ UNCHANGED <<seq, i, cand, cnt>>

NextAction == Next \/ NextStutter

\* Full specification *)
Spec == Init /\ [][NextAction]_<<seq, i, cand, cnt>>

\* Type correctness invariant *)
TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

\* Helper: number of occurrences of a value in a sequence *)
Count(s, v) ==
  Cardinality({ j \in DOMAIN s : s[j] = v })

\* Main correctness property: if a true majority exists, the final candidate equals it *)
Correct ==
  LET len == SeqLen(seq) IN
  /\ i > len
  /\ \E m \in Values : (Count(seq, m) * 2 > len) => cand = m

\* Inductive invariant used during the scan *)
Inv ==
  /\ cnt = 0
     \/ (cnt > 0 /\ cand \in Values
         /\ Count([j \in 1 .. (i - 1) |-> seq[j]], cand) >= cnt)

====