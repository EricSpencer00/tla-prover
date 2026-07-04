---- MODULE DistributedReplicatedLog ----
EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT Lag, Servers, Values
ASSUME Lag \in Nat /\ IsFiniteSet(Servers)

VARIABLE cLogs
vars == <<cLogs>>

TypeOK ==
    /\ cLogs \in [Servers -> Seq(Values)]

Init ==
    /\ cLogs \in [Servers -> {<< >>}]

(* Copy a missing suffix from a longer log.  A copy must increase the
   length of the destination log (at least one new element). *)
Copy(i) ==
    \E j \in Servers:
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ LET L == (Len(cLogs[j]) - Len(cLogs[i]))
           IN \E l \in 1 .. L:
                 cLogs' = [cLogs EXCEPT ![i] = @ \o SubSeq(cLogs[j],
                                                          Len(@) + 1,
                                                          Len(@) + l)]

(* Extend a log with a (possibly empty) sequence of new values, respecting
   the lag bound.  The pre‑condition that the server be the longest is
   removed so that every server can eventually extend. *)
Extend(i) ==
    /\ \E s \in BoundedSeq(Values,
                           Lag - Max({Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers})):
         cLogs' = [cLogs EXCEPT ![i] = @ \o s]

Next ==
    \E i \in Servers:
        \/ Copy(i)
        \/ Extend(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers: WF_vars(Extend(s)) /\ WF_vars(Copy(s))

(* Invariants *)

Abs(n) ==
    IF n < 0 THEN -n ELSE n

BoundedLag ==
    \A i, j \in Servers:
        Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

(* Liveness *)

AllExtending ==
    \A s \in Servers: []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====