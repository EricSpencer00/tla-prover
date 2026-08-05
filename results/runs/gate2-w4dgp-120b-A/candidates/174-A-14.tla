---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES color, msg, pc, sample, iteration

vars == <<color, msg, pc, sample, iteration>>

ColorOne == CHOOSE c \in {NoColor} \cup (UNION { {1} }) : TRUE
ColorTwo == CHOOSE c \in {NoColor} \cup (UNION { {2} }) : TRUE

TypeOK ==
    /\ color \in [Node -> {NoColor, ColorOne, ColorTwo}]
    /\ msg \subseteq {NoMessage} \cup ((Node \X Node) \X ({NoColor} \cup {ColorOne, ColorTwo}) \cup (Node \X Node) \cup (SlushLoopProcess \X {NoMessage}))
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} -> 0..3]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msg = {}
    /\ sample = [ln \in SlushLoopProcess |-> {}]
    /\ iteration = [ln \in SlushLoopProcess |-> 0]
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} |-> 0]

RequireColor(ln) ==
    /\ pc[ln] = 1
    /\ \E n \in Node : <<ln, n>> \in HostMapping /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![ln] = 2]
    /\ UNCHANGED <<color, msg, sample, iteration>>

QuerySampleSet(ln) ==
    /\ pc[ln] = 2
    /\ \E sampleSet \in SUBSET Node :
        /\ Cardinality(sampleSet) = SampleSetSize
        /\ sampleSet # {}
        /\ sampleSet # {n \in Node : <<ln, n>> \in HostMapping}
        /\ sample' = [sample EXCEPT ![ln] = sampleSet]
    /\ msg' = {<<ln, n, color[n]> : n \in sampleSet} \cup msg
    /\ pc' = [pc EXCEPT ![ln] = 3]
    /\ UNCHANGED <<color, iteration>>

RespondToQuery(n, ln, c) ==
    /\ <<ln, n>> \in msg
    /\ pc[n] = 0
    /\ LET host == CHOOSE m \in Node : <<n, m>> \in HostMapping
       IN LET hostColor == IF color[host] = NoColor THEN c ELSE color[host]
          IN /\ color' = [color EXCEPT ![host] = hostColor]
             /\ msg' = (msg \ {<<ln, n, c>>}) \cup {<<n, ln, hostColor>>}
    /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies(ln) ==
    /\ pc[ln] = 3
    /\ \A n \in sample[ln] : <<n, ln, color[n]>> \in msg
    /\ LET replies == {n \in sample[ln] : <<n, ln, color[n]>> \in msg}
           cOne == Cardinality({n \in replies : color[n] = ColorOne})
           cTwo == Cardinality({n \in replies : color[n] = ColorTwo})
       IN color' = [color EXCEPT
                      ![CHOOSE m \in Node : <<ln, m>> \in HostMapping] =
                        IF cOne >= PickFlipThreshold THEN ColorOne
                        ELSE IF cTwo >= PickFlipThreshold THEN ColorTwo
                        ELSE color[CHOOSE m \in Node : <<ln, m>> \in HostMapping]]
    /\ msg' = {m \in msg : m[1] # n} \cup {<<n, ln, color[n]>> : n \in replies}
    /\ sample' = [sample EXCEPT ![ln] = {}]
    /\ iteration' = [iteration EXCEPT ![ln] = IF iteration[ln] < SlushIterationCount THEN iteration[ln] + 1 ELSE iteration[ln]]
    /\ pc' = [pc EXCEPT ![ln] = IF iteration[ln] < SlushIterationCount THEN 1 ELSE 4]

LoopTerminate(ln) ==
    /\ pc[ln] = 4
    /\ msg' = msg \cup {<<ln, NoMessage>>}
    /\ UNCHANGED <<color, pc, sample, iteration>>

QueryLoopExit(n) ==
    /\ pc[n] = 0
    /\ \A ln \in SlushLoopProcess : msg' = msg \cup {<<n, ln>>}
    /\ pc' = [pc EXCEPT ![n] = 2]
    /\ UNCHANGED <<color, sample, iteration>>

AssignColor ==
    /\ pc["clientReq"] = 0
    /\ \E n \in Node, c \in {ColorOne, ColorTwo} :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT !["clientReq"] = 1]
    /\ UNCHANGED <<msg, sample, iteration>>

ReqIdle ==
    /\ pc["clientReq"] = 1
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["clientReq"] = 0]
    /\ UNCHANGED <<color, msg, sample, iteration>>

Next ==
    \/ AssignColor \/ ReqIdle
    \/ \E ln \in SlushLoopProcess : RequireColor(ln) \/ QuerySampleSet(ln) \/ TallyReplies(ln) \/ LoopTerminate(ln)
    \/ \E n \in SlushQueryProcess : QueryLoopExit(n)
    \/ \E n \in Node, ln \in SlushLoopProcess, c \in {NoColor, ColorOne, ColorTwo} : RespondToQuery(n, ln, c)

Spec == Init /\ [][Next]_vars /\ WF_vars(ReqIdle) /\ \A ln \in SlushLoopProcess : WF_vars(RequireColor(ln))

AllClientsTerminate ==
    \A ln \in SlushLoopProcess : pc[ln] = 4

====