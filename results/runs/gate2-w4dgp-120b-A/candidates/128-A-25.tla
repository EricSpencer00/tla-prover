---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Automorphisms

CONSTANTS Values, MaxSeqLen

SeqDom == 1..MaxSeqLen

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Restricted(x) == \A i \in DOMAIN x : x[i] \in Values

LimitedSeq(n) == { s \in SeqDom : n <= s /\ Restricted(s) }

TypeOK ==
    /\ seq \in SeqDom
    /\ orig \in SeqDom
    /\ work \subseteq (SeqDom \X SeqDom)
    /\ pc \in {"loop", "done"}

Partitioned(s, i, j) ==
    { t \in SeqDom :
          /\ \A k \in DOMAIN s : (k < i \/ k >= j) => t[k] = s[k]
          /\ \A k \in i..(j - 1) :
                \A l \in j..Len(s) : t[k] <= t[l] }

Init ==
    /\ \E s \in LimitedSeq(1) : seq = s /\ orig = s
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ \E a, b \in SeqDom :
         /\ <<a, b>> \in work
         /\ IF a = b THEN work' = work \ { <<a, b>> }
            ELSE \E k \in a..(b - 1) :
                /\ \E t \in Partitioned(seq, a, b) : seq' = t
                /\ work' = (work \ { <<a, b>> }) \cup { <<a, k>>, <<k + 1, b>> }
    /\ pc' = "loop"

Terminate ==
    /\ pc = "loop"
    /\ work = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, work>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Terminate
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

PCorrect ==
    (pc = "done") => (seq = orig /\ \A i \in DOMAIN seq : \A j \in DOMAIN seq : i < j => seq[i] <= seq[j])

Inv ==
    /\ (work = {} => seq = orig)
    /\ (\A a, b \in SeqDom :
        <<a, b>> \in work =>
            /\ a \in DOMAIN seq /\ b \in DOMAIN seq
            /\ \A i, j \in a..b : i <= j => seq[i] <= seq[j])
    /\ (\A a, b \in SeqDom :
        <<a, b>> \in work =>
            \A \sigma \in Aut(SeqDom) :
                (\A i \in SeqDom : seq[i] = orig[i]) => seq[i] = orig[\sigma[i]])
    /\ (\A i \in DOMAIN seq : seq[i] \in Values)

Termination == Spec => <>(pc = "done")

====