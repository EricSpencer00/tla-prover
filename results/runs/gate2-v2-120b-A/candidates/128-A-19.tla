---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants required by the .cfg
-----------------------------------------------------------------*)
CONSTANTS Values, MaxSeqLen, Seq

(*-----------------------------------------------------------------
  Definitions of auxiliary concepts
-----------------------------------------------------------------*)
\* Index range for a sequence of length n (1..n)
Idx(n) == 1 .. n

\* An interval is a pair <<a, b>> with a <= b and both in the index range
Interval(n) == { <<a, b>> : a \in Idx(n), b \in Idx(n), a <= b }

\* Permutation defined as a bijection on the index set
Perm(n) == { f \in [Idx(n) -> Idx(n)] : \A i, j \in Idx(n) : f[i] = f[j] => i = j }

\* Apply a permutation to a sequence
ApplyPerm(s, f) ==
  [i \in Idx(Len(s)) |-> s[f[i]]]

\* All permutations that leave indices outside the given interval unchanged
FixedOutsidePerm(s, i, j) ==
  { f \in Perm(Len(s)) :
      \A k \in Idx(Len(s)) :
        (k < i \/ k > j) => f[k] = k }

\* Partition operation: any permuted sequence that respects the pivot
Partition(s, i, j, p) ==
  { s1 \in Seq(Len(s)) :
      \A k \in Idx(Len(s)) :
        (k < i \/ k > j) => s1[k] = s[k] /\
      \A k \in i .. p : \A l \in (p+1) .. j : s1[k] <= s1[l] }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES seq, orig, work, pc

(*-----------------------------------------------------------------
  State predicates
-----------------------------------------------------------------*)
Sorted(t) ==
  \A i, j \in Idx(Len(t)) : i < j => t[i] <= t[j]

Permutation(t, s) ==
  \E f \in Perm(Len(t)) : t = ApplyPerm(s, f)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ seq = Seq
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

(*-----------------------------------------------------------------
  Main transition (one iteration of the sorting loop)
-----------------------------------------------------------------*)
Run ==
  \/ /\ work # {}
     /\ \E int \in work :
          LET i == int[1]
              j == int[2]
          IN
          IF i = j THEN
            /\ work' = work \ {int}
            /\ UNCHANGED <<seq, orig>>
          ELSE
            /\ \E p \in i .. j :
                 /\ \E s1 \in Partition(seq, i, j, p) :
                       /\ seq' = s1
                       /\ work' = (work \ {int}) \cup { <<i, p>>, <<p+1, j>> }
                       /\ UNCHANGED orig
  \/ /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>

Next ==
  \/ Run
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<seq, orig, work, pc>>

(*-----------------------------------------------------------------
  Invariant used for model checking
-----------------------------------------------------------------*)
Inv ==
  /\ Permutation(seq, orig)
  /\ \A int \in work :
        LET i == int[1]
            j == int[2]
        IN Sorted(seq[i .. j])
  /\ \A i, j \in Idx(Len(seq)) :
        ( \E int \in work : i \in Idx(int[2]) /\ j \in Idx(int[2]) ) => 
          (i < j => seq[i] <= seq[j])

(*-----------------------------------------------------------------
  Safety properties
-----------------------------------------------------------------*)
PCorrect ==
  pc = "Done" => /\ Permutation(seq, orig)
                 /\ Sorted(seq)

TypeOK ==
  /\ seq \in Seq(Len(seq))
  /\ orig \in Seq(Len(seq))
  /\ work \subseteq Interval(Len(seq))
  /\ pc \in {"Run", "Done"}

Termination ==
  <> (pc = "Done")

=============================================================================