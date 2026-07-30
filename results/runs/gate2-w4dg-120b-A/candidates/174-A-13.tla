---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    HostMapping,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

Messages == [type: {"query", "reply", "term"}, proc: SlushLoopProcess \cup SlushQueryProcess, color: {NoColor, "red", "blue"}]

VARIABLES assignedColor, messages, pc, sample, iters

vars == <<assignedColor, messages, pc, sample, iters>>

TypeOK ==
    /\ assignedColor \in [Node -> {NoColor, "red", "blue"}]
    /\ messages \subseteq Messages
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"assign", "query", "wait", "tally", "done", "exited"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ assignedColor = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> IF p = "client" THEN "assign" ELSE "query"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iters = [p \in SlushLoopProcess |-> 0]

AssignColor ==
    /\ pc["client"] = "assign"
    /\ \E n \in Node :
        /\ assignedColor[n] = NoColor
        /\ \E col \in {"red", "blue"} : assignedColor' = [assignedColor EXCEPT ![n] = col]
    /\ pc' = [pc EXCEPT !["client"] = "query"]
    /\ UNCHANGED <<messages, sample, iters>>

RequireColor ==
    /\ \A p \in SlushLoopProcess :
        /\ pc[p] = "query" => \E n \in Node : <<n, p, "query">> \in HostMapping /\ assignedColor[n] # NoColor
    /\ UNCHANGED vars

QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
        /\ pc[p] = "query"
        /\ iters[p] < SlushIterationCount
        /\ \E peers \in SUBSET SlushQueryProcess :
            /\ peers # {}
            /\ \E n \in Node :
                /\ \E q \in SlushQueryProcess : <<n, q, "query">> \in HostMapping
                /\ \A r \in peers : <<n, r, "query">> \in HostMapping
                /\ sample' = [sample EXCEPT ![p] = peers]
                /\ messages' = messages \cup {[type |-> "query", proc |-> q, color |-> assignedColor[n]] : q \in peers}
            /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<assignedColor, iters>>

RespondToQuery ==
    /\ \E q \in SlushQueryProcess :
        /\ \E m \in messages :
            /\ m.type = "query" /\ m.proc = q /\ assignedColor' = [assignedColor EXCEPT ![HostMapping[m.proc].n] = IF assignedColor[HostMapping[m.proc].n] = NoColor THEN m.color ELSE assignedColor[HostMapping[m.proc].n]]
            /\ messages' = (messages \ {m}) \cup {[type |-> "reply", proc |-> q, color |-> assignedColor[HostMapping[m.proc].n]]}
    /\ UNCHANGED <<pc, sample, iters>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
        /\ pc[p] = "wait"
        /\ \A q \in sample[p] : [type |-> "reply", proc |-> q, color |-> assignedColor[HostMapping[q].n]] \in messages
        /\ LET votes == [c \in {"red", "blue"} |-> Cardinality({q \in sample[p] : assignedColor[HostMapping[q].n] = c})]
           IN assignedColor' = [assignedColor EXCEPT ![HostMapping[p].n] = IF votes["red"] >= PickFlipThreshold THEN "red" ELSE IF votes["blue"] >= PickFlipThreshold THEN "blue" ELSE assignedColor[HostMapping[p].n]]
        /\ messages' = {m \in messages : ~(m.type = "reply" /\ m.proc \in sample[p])}
        /\ sample' = [sample EXCEPT ![p] = {}]
        /\ iters' = [iters EXCEPT ![p] = @ + 1]
        /\ pc' = [pc EXCEPT ![p] = IF iters[p] + 1 = SlushIterationCount THEN "done" ELSE "query"]
    /\ UNCHANGED <<>>

LoopTermination ==
    /\ \E p \in SlushLoopProcess :
        /\ pc[p] = "done"
        /\ messages' = messages \cup {[type |-> "term", proc |-> p, color |-> NoColor]}
        /\ pc' = [pc EXCEPT ![p] = "exited"]
    /\ UNCHANGED <<assignedColor, sample, iters>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
        /\ pc[q] # "exited"
        /\ \A p \in SlushLoopProcess : pc[p] = "exited"
        /\ pc' = [pc EXCEPT ![q] = "exited"]
    /\ UNCHANGED <<assignedColor, messages, sample, iters>>

Next ==
    \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

AllExited == \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pc[p] = "exited"

Termination == <>(AllExited)

====