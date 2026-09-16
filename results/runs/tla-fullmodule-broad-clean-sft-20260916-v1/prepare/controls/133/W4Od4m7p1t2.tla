---------------------------- MODULE W4Od4m7p1t2 ----------------------------
EXTENDS Naturals
CONSTANTS Instances, MaxSeq, MaxVer, NONE

VARIABLES reg, ver, committed, pending, seq

vars == <<reg, ver, committed, pending, seq>>

WriteIds == {<<i, k>> : i \in Instances, k \in 1..MaxSeq}
Proposals == [id : WriteIds, base : 0..MaxVer]

TypeOK ==
    /\ reg \subseteq WriteIds
    /\ ver \in 0..MaxVer
    /\ committed \subseteq WriteIds
    /\ pending \in [Instances -> Proposals \cup {NONE}]
    /\ seq \in [Instances -> 0..MaxSeq]

Init ==
    /\ reg = {}
    /\ ver = 0
    /\ committed = {}
    /\ pending = [i \in Instances |-> NONE]
    /\ seq = [i \in Instances |-> 0]

Read(i) ==
    /\ pending[i] = NONE
    /\ seq[i] < MaxSeq
    /\ pending' = [pending EXCEPT ![i] = [id |-> <<i, seq[i] + 1>>, base |-> ver]]
    /\ seq' = [seq EXCEPT ![i] = seq[i] + 1]
    /\ UNCHANGED <<reg, ver, committed>>

CommitCAS(i) ==
    /\ pending[i] # NONE
    /\ pending[i].base = ver
    /\ ver < MaxVer
    /\ reg' = reg \cup {pending[i].id}
    /\ committed' = committed \cup {pending[i].id}
    /\ ver' = ver + 1
    /\ pending' = [pending EXCEPT ![i] = NONE]
    /\ UNCHANGED <<seq>>

RetryCAS(i) ==
    /\ pending[i] # NONE
    /\ pending[i].base # ver
    /\ pending' = [pending EXCEPT ![i] = NONE]
    /\ UNCHANGED <<reg, ver, committed, seq>>

NewShift ==
    /\ ver > 0
    /\ reg' = {}
    /\ ver' = 0
    /\ committed' = {}
    /\ pending' = [i \in Instances |-> NONE]
    /\ seq' = [i \in Instances |-> 0]

Next ==
    \/ \E i \in Instances : Read(i)
    \/ \E i \in Instances : CommitCAS(i)
    \/ \E i \in Instances : RetryCAS(i)
    \/ NewShift

Spec == Init /\ [][Next]_vars

NoLostUpdate ==
    committed \subseteq reg
=============================================================================