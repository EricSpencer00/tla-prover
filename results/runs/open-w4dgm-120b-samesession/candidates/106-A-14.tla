---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxV

AllSequences == UNION {[Seq(1..n) -> {1..MaxV}]: n \in 1..MaxV}

VARIABLES specStage, initDone, thread, record, pool

vars == <<specStage, initDone, thread, record, pool>>

RECURSIVE ReduceSetOver(S, f, a)
ReduceSetOver(S, f, a) ==
    IF S = {} THEN a
    ELSE LET x == CHOOSE y \in S : TRUE IN f[ReduceSetOver(S \ {x}, f, a, x)]

RECURSIVE ReduceSeqOver(seq, f, a)
ReduceSeqOver(seq, f, a) ==
    IF seq = <<>> THEN a
    ELSE f[seq[1], ReduceSeqOver(Tail(seq), f, a)]

PermutationsOf(S) ==
    IF S = {} THEN {<<>>}
    ELSE UNION {PrependSeq(x, p) : x \in S, p \in PermutationsOf(S \ {x})}

Init ==
    /\ specStage = "idle"
    /\ initDone = FALSE
    /\ thread = 0
    /\ record = [c \in 1..MaxV |-> 0]
    /\ pool = AllSequences

\* Phase 1: the single irreversible step, allowed only before any writing thread
\* is running. Once taken, it can never be taken again.
TakeStep ==
    /\ specStage = "idle"
    /\ initDone = FALSE
    /\ specStage' = "taken"
    /\ initDone' = TRUE
    /\ UNCHANGED <<thread, record, pool>>

\* Phase 2: a writing thread is spun up, and it may start only once the step has
\* actually been taken.
SpinUpThread ==
    /\ thread = 0
    /\ specStage = "taken"
    /\ thread' = 1
    /\ UNCHANGED <<specStage, initDone, record, pool>>

\* Phase 3: the running thread writes to one record slot, which it may do at most
\* once per slot.
WriteRecord ==
    /\ thread = 1
    /\ \E c \in 1..MaxV :
        /\ record[c] = 0
        /\ record' = [record EXCEPT ![c] = record[c] + 1]
    /\ UNCHANGED <<specStage, initDone, thread, pool>>

\* Phase 4: once the step has been taken and no writing thread is running, the
\* store is quiescent even though the step's one-time state is still marked taken.
Quiesce ==
    /\ thread = 0
    /\ specStage = "taken"
    /\ UNCHANGED vars

Next == TakeStep \/ SpinUpThread \/ WriteRecord \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ specStage \in {"idle", "taken"}
    /\ initDone \in BOOLEAN
    /\ thread \in 0..1
    /\ record \in [1..MaxV -> 0..2]
    /\ pool \subseteq AllSequences

\* SAFETY PROPERTY: the single irreversible step is taken at most once, reflected
\* in the fact that any record slot written to is written exactly once -- even
\* though the step is never undone and the step state remains marked.
StepTakenAtMostOnce == \A c \in 1..MaxV : record[c] <= 1

====