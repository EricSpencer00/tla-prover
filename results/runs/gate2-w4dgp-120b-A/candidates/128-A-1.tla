---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

Domain == 1 .. MaxSeqLen

VARIABLES seq, orig, todo, pc

vars == << seq, orig, todo, pc >>

RECURSIVE Permutation(_, _)
Permutation(s, f) == IF f = {} THEN s
                      ELSE LET x == CHOOSE y \in f : TRUE IN
                           LET i == CHOOSE j \in Domain : s[j] = x IN
                           LET t == [j \in Domain |-> IF j = i THEN s[f[x]] ELSE IF j = f[x] THEN x ELSE s[j]] IN
                           Permutation(t, f \ {x})

TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ Len(orig) <= MaxSeqLen
    /\ todo \subseteq (Domain \X Domain)
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in Seq(Values) : Len(s) >= 1 /\ seq = s /\ orig = s
    /\ todo = {<<1, Len(seq)>>}
    /\ pc = "loop"

LimitedSeq(s) == s \in Seq(Values) /\ Len(s) <= MaxSeqLen

Partition(s, lo, hi, pi) ==
    {t \in Seq(Values) :
        /\ Len(t) = Len(s)
        /\ \A k \in Domain : (k < lo \/ k > hi) => t[k] = s[k]
        /\ \A i, j \in lo..hi : (i <= pi /\ pi < j) => t[i] <= t[j]}

SortStep ==
    /\ pc = "loop"
    /\ todo # {}
    /\ \E p \in todo :
         /\ IF p[1] = p[2]
            THEN /\ todo' = todo \ {p}
                 /\ UNCHANGED <<seq, orig>>
            ELSE /\ \E pi \in p[1]..p[2] :
                  /\ \E t \in Partition(seq, p[1], p[2], pi) :
                        /\ seq' = t
                        /\ todo' = (todo \ {p}) \cup {<<p[1], pi>>, <<pi + 1, p[2]>>}
            /\ UNCHANGED orig
    /\ pc' = "loop"

Halt ==
    /\ pc = "loop"
    /\ todo = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, todo>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == SortStep \/ Halt \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep \/ Halt)

WellSorted(s, lo, hi) ==
    \A i, j \in lo..hi : i < j => s[i] <= s[j]

DomainPartition ==
    LET rd[j \in Domain] == IF j = 1 THEN 1 ELSE
                              (IF \E p \in todo : p[1] <= j - 1 /\ p[2] >= j - 1 THEN rd[j - 1] ELSE rd[j - 1] + 1) IN
    rd[MaxSeqLen] = rd[1] + Cardinality(todo)

Inv ==
    /\ DomainPartition
    /\ Permutation(seq, orig)
    /\ \A lo, hi \in Domain : (lo, hi) \in todo => WellSorted(seq, lo, hi)

PCorrect ==
    (pc = "done") => (Permutation(seq, orig) /\ WellSorted(seq, 1, Len(seq)))

Termination == <>(pc = "done")

====