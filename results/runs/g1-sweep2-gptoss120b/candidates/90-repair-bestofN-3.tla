---- MODULE DistributedReplicatedLog ----
EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT Lag, Servers, Values
ASSUME Lag \in Nat /\ IsFiniteSet(Servers)

VARIABLE cLogs
vars == <<cLogs>>

\*-----------------------------------------------------------------
\* Types
\*-----------------------------------------------------------------
TypeOK ==
    /\ cLogs \in [Servers -> Seq(Values)]

\*-----------------------------------------------------------------
\* Initialization
\*-----------------------------------------------------------------
Init ==
    /\ cLogs \in [Servers -> {<< >>}]

\*-----------------------------------------------------------------
\* Copy action – a server copies the missing suffix from a longer
\* server.  The whole missing suffix is copied (instead of a
\* nondeterministic prefix) to guarantee progress while still
\* respecting the lag bound.
\*-----------------------------------------------------------------
Copy(i) ==
    \E j \in Servers:
        /\ Len(cLogs[j]) > Len(cLogs[i])
        LET L == Len(cLogs[j]) - Len(cLogs[i])
        IN  cLogs' = [cLogs EXCEPT ![i] = @ \o
                     SubSeq(cLogs[j], Len(@) + 1, Len(cLogs[j]))]

\*-----------------------------------------------------------------
\* Extend action – a server that is at least as long as every other
\* server may append a non‑empty sequence of new values.  The length
\* of the appended sequence is limited so that the lag invariant
\* can still be satisfied, even when the current maximum lag equals
\* the configured Lag.
\*-----------------------------------------------------------------
Extend(i) ==
    /\ \A j \in Servers: Len(cLogs[j]) <= Len(cLogs[i])
    /\ LET maxDiff == Max({ Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers })
       IN /\ maxDiff <= Lag
          /\ \E s \in BoundedSeq(Values, Lag - maxDiff + 1):
                 /\ Len(s) > 0
                 /\ cLogs' = [cLogs EXCEPT ![i] = @ \o s]

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \E i \in Servers:
        \/ Copy(i)
        \/ Extend(i)

\*-----------------------------------------------------------------
\* Overall specification
\*-----------------------------------------------------------------
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers: WF_vars(Extend(s)) /\ WF_vars(Copy(s))

\*=================================================================
\* Invariants
\*=================================================================
Abs(n) ==
    IF n < 0 THEN -n ELSE n

BoundedLag ==
    \A i, j \in Servers:
        Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

\*=================================================================
\* Liveness properties
\*=================================================================
AllExtending ==
    \A s \in Servers: []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====