---- MODULE DistributedReplicatedLog ----
EXTENDS Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt, Apalache

CONSTANT
  \* @type: Int;
  Lag,
  \* @type: Set(Str);
  Servers,
  \* @type: Set(Str);
  Values
ASSUME Lag \in Nat /\ IsFiniteSet(Servers)

VARIABLE
  \* @type: Str -> Seq(Str);
  cLogs
\* @type: <<Str -> Seq(Str)>>;
vars == <<cLogs>>

TypeOK ==
    /\ DOMAIN cLogs = Servers
    /\ \A s \in Servers : \A i \in DOMAIN cLogs[s] : cLogs[s][i] \in Values
    
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
    /\ \A j \in Servers:
            Len(cLogs[j]) \leq Len(cLogs[i])
    \* BoundedSeq(Values, n) unfolded for Apalache (unsupported operator, see
    \* APALACHE_FINDINGS.md spec 92 note): pick a length first, then a
    \* function of that exact length, instead of UNION-ing a family of
    \* function-sets by name.
    /\ LET maxLag == Lag - Max({Len(cLogs[i]) - Len(cLogs[j]) : j \in Servers}) IN
       \E l \in 0..maxLag :
         \E s \in [1..Lag -> Values] :  \* fixed-capacity domain (Lag is a CONSTANT); FunAsSeq truncates to length l
            cLogs' = [cLogs EXCEPT ![i] = @ \o FunAsSeq(s, l, Lag)]

Next ==
    \E i \in Servers: 
        \/ Copy(i) 
        \/ Extend(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Servers: WF_vars(Extend(s)) /\ WF_vars(Copy(s))

----
\* Invariants

Abs(n) ==
    IF n < 0 THEN -n ELSE n

BoundedLag ==
    \A i, j \in Servers: Abs(Len(cLogs[i]) - Len(cLogs[j])) <= Lag

THEOREM Spec => []BoundedLag

----
\* Liveness

AllExtending ==
    \A s \in Servers: []<><<IsStrictPrefix(cLogs[s], cLogs'[s])>>_cLogs

THEOREM Spec => AllExtending

InSync ==
    \* TLC correctly verifies that InSync is not a property of the system because
    \* followers are permitted to copy only a prefix of the missing suffix.
    \A i, j \in Servers : []<>(cLogs[i] = cLogs[j])

====
