---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

VARIABLES seq, original, toProcess, pc

vars == <<seq, original, toProcess, pc>>

Domain == 1 .. Len(seq)

Interval == [lo : Nat, hi : Nat]

Empty == [lo |-> 0, hi |-> 0]

SMALLER(i, j) == \A a \in Domain, b \in Domain :
                    (i <= a /\ b <= j) => seq[a] <= seq[b]

Lower(i, j) == [lo |-> i, hi |-> j]

IntervalOf(x) == Lower(1, Len(seq))

INTERLEAVING == UNION { UNION { AllSeqs([1 .. k], Values) : k \in 1 .. MaxSeqLen } }

RECURSIVE PermAt(_, _)
PermAt(f, S) == IF S = {} THEN {} ELSE LET x == CHOOSE x \in S : TRUE IN {f[x]} UNION PermAt(f, S \ {x})

Permutations == { g \in [Domain -> Values] : PermAt(g, Domain) = INTERLEAVING }

BoundedPartition(i, j, k) == { p \in Permutations :
                                 (\A m \in Domain : m < i \/ j < m => p[m] = seq[m])
                                   /\ (\A a \in Domain, b \in Domain : (i <= a /\ b <= k) \/ (k < a /\ b <= j) => p[a] <= p[b]) }

TypeOK ==
  /\ seq \in INTERLEAVING
  /\ original \in INTERLEAVING
  /\ toProcess \subseteq (INTERVAL)
  /\ pc \in {"main"}

PCorrect ==
  /\ (pc = "done" => \A i \in Domain : \A j \in Domain : SMALLER(i, j))
  /\ (pc = "done" => PermAt(seq, Domain) = PermAt(original, Domain))

Init ==
  /\ seq \in { s \in INTERLEAVING : Len(s) > 0 }
  /\ original = seq
  /\ toProcess = {IntervalOf(seq)}
  /\ pc = "main"

SortStep ==
  /\ pc = "main"
  /\ \E r \in toProcess :
       /\ IF r.lo = r.hi
            THEN toProcess' = toProcess \ {r}
            ELSE \E k \in (r.lo + 1) .. r.hi :
                   \E p \in BoundedPartition(r.lo, r.hi, k) :
                     /\ seq' = [seq EXCEPT ![m \in Domain] = p[m]]
                     /\ toProcess' = (toProcess \ {r}) \union {Lower(r.lo, k), Lower(k + 1, r.hi)}
  /\ pc' = "main"

Crash ==
  /\ pc = "main"
  /\ toProcess = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, toProcess>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Crash \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep \/ Crash)

Termination == (pc = "done") ~> (pc = "done")
====