---- MODULE DistributedReplicatedLog ----
EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT Lag, Servers, Values
ASSUME Lag \in Nat /\ IsFiniteSet(Servers)

VARIABLE cLogs
vars == <<cLogs>>

(* ----------------------------------------------------------------------
   Type correctness
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ cLogs \in [Servers -> Seq(Values)]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ cLogs \in [Servers -> {<< >>}]

(* ----------------------------------------------------------------------
   Copy action – a server i copies a non‑empty prefix of the missing suffix
   from a server j that is ahead.
   ---------------------------------------------------------------------- *)
Copy(i) ==
    \E j \in Servers :
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ LET L == Len(cLogs[j]) - Len(cLogs[i]) IN
            \E l \in 1 .. L :
                cLogs' = [cLogs EXCEPT ![i] = @ \o SubSeq(cLogs[j],
                                                       Len(@) + 1,
                                                       Len(@) + l)]

(* ----------------------------------------------------------------------
   Extend action – a server i that is at least as long as every other server
   may append a non‑empty bounded sequence of values, respecting the lag bound.
   ---------------------------------------------------------------------- *)
Extend(i) ==
    /\ \A j \in Servers : Len(cLogs[j]) <= Len(cLogs[i])
    /\ \E s \in BoundedSeq(Values,
                           Lag - Max({ Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers })):
           /\ Len(s) >= 1
           cLogs' = [cLogs EXCEPT ![i] = @ \o s]

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \E i \in Servers :
        \/ Copy(i)
        \/ Extend(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers : WF_vars(Extend(s)) /\ WF_vars(Copy(s))

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
Abs(n) ==
    IF n < 0 THEN -n ELSE n

BoundedLag ==
    \A i, j \in Servers :
        Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

(* ----------------------------------------------------------------------
   Liveness properties
   ---------------------------------------------------------------------- *)
AllExtending ==
    \A s \in Servers : []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====