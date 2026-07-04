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

(* Copy the missing suffix from a longer log to a shorter one.
   The missing suffix is copied completely, ensuring that logs can
   eventually converge. *)
Copy(i) ==
    \E j \in Servers:
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ LET missing == Len(cLogs[j]) - Len(cLogs[i])
           IN cLogs' = [cLogs EXCEPT ![i] = @ \o SubSeq(cLogs[j],
                                                      Len(@) + 1,
                                                      Len(cLogs[j]))]

Extend(i) ==
    /\ \A j \in Servers:
            Len(cLogs[j]) \leq Len(cLogs[i])
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
    \A i, j \in Servers: Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

(* Liveness *)

AllExtending ==
    \A s \in Servers: []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====