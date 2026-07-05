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

Copy(i) ==
    \E j \in Servers: 
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ \* Sync some prefix up to prefix = suffix of the unsynced suffix.
           LET L == (Len(cLogs[j]) - Len(cLogs[i]))
           \* Force to proportionally to the lag L copy more.
           \* Lag: 1 -> 0..L, 2 -> 1..L, 3 -> 2..L 
           IN  \E l \in L-1 .. L:
                    cLogs' = [cLogs EXCEPT ![i] = @ \o SubSeq(cLogs[j], Len(@) + 1, Len(@) + l)]

Extend(i) ==
    /\ \E s \in BoundedSeq(Values, Lag - Max({Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers})):
            cLogs' = [cLogs EXCEPT ![i] = @ \o s]

Next ==
    \E i \in Servers: 
        \/ Copy(i) 
        \/ Extend(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers: WF_vars(Extend(s)) /\ WF_vars(Copy(s))

====