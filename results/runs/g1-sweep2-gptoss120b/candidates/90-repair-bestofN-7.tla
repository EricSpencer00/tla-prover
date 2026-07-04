---- MODULE DistributedReplicatedLog ----
EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT Lag, Servers, Values
ASSUME Lag \in Nat /\ IsFiniteSet(Servers)

VARIABLE cLogs
vars == <<cLogs>>

\*-----------------------------------------------------------------
\* Type invariant
\*-----------------------------------------------------------------
TypeOK ==
    /\ cLogs \in [Servers -> Seq(Values)]

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ cLogs \in [Servers -> {<< >>}]

\*-----------------------------------------------------------------
\* Copy action – a server copies a (possibly partial) suffix from a
\* longer server, respecting the configured lag.
\*-----------------------------------------------------------------
Copy(i) ==
    \E j \in Servers:
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ LET L == (Len(cLogs[j]) - Len(cLogs[i]))
           IN \E l \in L-1 .. L:
                cLogs' = [cLogs EXCEPT ![i] = @ \o SubSeq(cLogs[j],
                                                       Len(@) + 1,
                                                       Len(@) + l)]

\*-----------------------------------------------------------------
\* Extend action – a server appends a bounded sequence of values.
\* The guard that required the server to be the longest has been
\* removed so that every server can eventually extend, preserving the
\* BoundedLag invariant.
\*-----------------------------------------------------------------
Extend(i) ==
    /\ \E s \in BoundedSeq(Values,
                          Lag - Max({Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers})):
           cLogs' = [cLogs EXCEPT ![i] = @ \o s]

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \E i \in Servers:
        \/ Copy(i)
        \/ Extend(i)

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers: WF_vars(Extend(s)) /\ WF_vars(Copy(s))

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
Abs(n) ==
    IF n < 0 THEN -n ELSE n

BoundedLag ==
    \A i, j \in Servers:
        Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

\*-----------------------------------------------------------------
\* Liveness properties
\*-----------------------------------------------------------------
AllExtending ==
    \A s \in Servers: []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====