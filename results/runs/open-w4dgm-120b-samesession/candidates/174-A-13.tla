---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

(* Slush: a metastable consensus protocol from the Avalanche family. Nodes    *)
(* repeatedly poll random peers and adopt a popular color, converging on a     *)
(* single color.  Actions: client assigns colors, loop processes poll peers,    *)
(* query processes reply, and loops terminate after a bounded round count.     *)

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

ASSUME HostMapping \in [SlushLoopProcess -> Node \X SlushQueryProcess]

Message == [kind: {qry, rsp, quit}, body: Node \union {NoColor},
            src: SlushQueryProcess \union SlushLoopProcess,
            dst: SlushLoopProcess \union SlushQueryProcess]
Loop(src, dst) == [src |-> src, dst |-> dst]

VARIABLES assign, inbox, pc, sample, loops

vars == <<assign, inbox, pc, sample, loops>>

Bump(i) == IF i < SlushIterationCount THEN i + 1 ELSE i

TypeOK ==
    /\ assign \in [Node -> {NoColor} \union {"red", "blue"}]
    /\ inbox \subseteq Message
    /\ pc \in [SlushLoopProcess -> {"waiting", "polling",
                                   "collecting", "done"}]
    /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ assign = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [i \in SlushLoopProcess |-> "waiting"]
    /\ sample = [i \in SlushLoopProcess |-> {}]
    /\ loops = [i \in SlushLoopProcess |-> 0]

ClientAssign ==
    \E n \in Node, c \in {"red", "blue"} :
        /\ assign[n] = NoColor
        /\ assign' = [assign EXCEPT ![n] = c]
        /\ UNCHANGED <<inbox, pc, sample, loops>>

RequireColor ==
    \E i \in SlushLoopProcess :
        /\ pc[i] = "waiting"
        /\ assign[HostMapping[i][1]] # NoColor
        /\ pc' = [pc EXCEPT ![i] = "polling"]
        /\ UNCHANGED <<assign, inbox, sample, loops>>

QuerySet ==
    \E i \in SlushLoopProcess :
        /\ pc[i] = "polling"
        /\ loops[i] < SlushIterationCount
        /\ sample[i] = {}
        /\ \E peers \in [SlushQueryProcess -> BOOLEAN] :
            /\ Cardinality({q \in SlushQueryProcess : peers[q]}) = SampleSetSize
            /\ sample' = [sample EXCEPT ![i] = peers]
        /\ inbox' = inbox \union
            {[kind |-> "qry", body |-> assign[HostMapping[i][1]],
              src |-> i, dst |-> q] : q \in SlushQueryProcess : sample[i][q]}
        /\ pc' = [pc EXCEPT ![i] = "collecting"]
        /\ UNCHANGED <<assign, loops>>

RespondQuery ==
    \E q \in SlushQueryProcess, m \in inbox :
        /\ m.kind = "qry"
        /\ m.dst = q
        /\ assign' = [n \in Node |-> IF n = HostMapping[m.src][1]
                                      THEN IF assign[n] = NoColor
                                           THEN m.body ELSE assign[n]
                                      ELSE assign[n]]
        /\ inbox' = (inbox \ {m}) \union
            {[kind |-> "rsp", body |-> assign[HostMapping[m.src][1]],
              src |-> q, dst |-> m.src]}
        /\ UNCHANGED <<pc, sample, loops>>

TallyReplies ==
    \E i \in SlushLoopProcess :
        /\ pc[i] = "collecting"
        /\ sample[i] # {}
        /\ \A q \in SlushQueryProcess : sample[i][q] =>
            \E m \in inbox : m.kind = "rsp" /\ m.dst = i /\ m.src = q
        /\ LET reds == Cardinality({q \in SlushQueryProcess :
                                        sample[i][q] /\ assign[HostMapping[i][1]] = "red"}),
               blues == Cardinality({q \in SlushQueryProcess :
                                        sample[i][q] /\ assign[HostMapping[i][1]] = "blue"})
           IN assign' = [assign EXCEPT ![HostMapping[i][1]] =
                IF reds >= PickFlipThreshold
                    THEN "red" ELSE IF blues >= PickFlipThreshold
                    THEN "blue" ELSE assign[HostMapping[i][1]]]
        /\ inbox' = {m \in inbox : ~(m.kind = "rsp" /\ m.dst = i)}
        /\ sample' = [sample EXCEPT ![i] = {}]
        /\ loops' = [loops EXCEPT ![i] = Bump(loops[i])]
        /\ pc' = [pc EXCEPT ![i] = IF loops[i] + 1 = SlushIterationCount
                                   THEN "done" ELSE "polling"]

QuitLoop ==
    /\ \E i \in SlushLoopProcess :
        /\ pc[i] = "done"
        /\ ~(\E m \in inbox : m.kind = "quit" /\ m.dst = i)
        /\ inbox' = inbox \union {Loop(i, NoMessage) [kind |-> "quit", body |-> NoColor]}
    /\ UNCHANGED <<assign, pc, sample, loops>>

QueryLoopExit ==
    /\ \A i \in SlushLoopProcess : pc[i] = "done"
    /\ \A q \in SlushQueryProcess :
        ~(\E m \in inbox : m.kind = "qry" /\ m.dst = q)
    /\ \A i \in SlushLoopProcess :
        ~(\E m \in inbox : m.kind = "rsp" /\ m.dst = i)
    /\ UNCHANGED vars

Next ==
    \/ ClientAssign \/ RequireColor \/ QuerySet \/ RespondQuery
    \/ TallyReplies \/ QuitLoop \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
    /\ WF_vars(ClientAssign) /\ WF_vars(RequireColor)
    /\ WF_vars(QuerySet) /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies)
    /\ WF_vars(QuitLoop) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == <>(\A i \in SlushLoopProcess : pc[i] = "done")
====