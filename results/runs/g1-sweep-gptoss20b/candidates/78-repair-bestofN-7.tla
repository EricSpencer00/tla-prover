---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* Trace validation has been designed for TLC running in default model-checking
 \* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

\* Deserialize the System log as a sequence of records from the log file.
\* Run TLC with (assuming a suitable "tlc" shell alias):
\* $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
\* Fall back to trace.ndjson if the JSON environment variable is not set.
\* The original expression used IOEnv.JSON which triggers an unbounded CHOOSE during
\* configuration evaluation.  We replace it with a constant file name so that
\* the JSON is read only during model checking.
JsonLog ==
    ndJsonDeserialize("specifications/ewd998/EWD998ChanTrace.ndjson")

TraceN ==
    JsonLog[1].N

TraceLog ==
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    IN CausalOrder(suffix,
                   LAMBDA l : l.pkt.vc,
                   LAMBDA l : ToString(l.node),
                   LAMBDA vc : DOMAIN vc)

TraceInit ==
    /\ Init!1
    /\ Init!2
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]

TraceSpec ==
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

PayloadPred(msg) ==
    msg.type = "pl"

IsInitiateToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    /\ l.pkt.rcv = N - 1
    /\ l.pkt.snd = 0
    /\ <<InitiateProbe>>_vars

IsPassToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    LET snd == l.pkt.snd IN
        /\ l.pkt.snd > 0
        /\ <<PassToken(snd)>>_vars

IsRecvToken(l) ==
    /\ l.event = "<"
    LET msg == l.pkt.msg
        rcv == l.pkt.rcv IN
        /\ msg.type = "tok"
        /\ \A n \in Node:
                SelectSeq(inbox[n], PayloadPred) = SelectSeq(inbox'[n], PayloadPred)
        /\ \E idx \in DOMAIN inbox'[rcv]:
            /\ inbox'[rcv][idx].type = "tok"
            /\ inbox'[rcv][idx].q = msg.q
            /\ inbox'[rcv][idx].color = msg.color
        /\ UNCHANGED <<active, counter, color>>

IsSendMsg(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "pl"
    /\ <<SendMsg(l.pkt.snd)>>_vars
    LET rcv == l.pkt.rcv IN
        /\ Len(SelectSeq(inbox[rcv], PayloadPred)) <
           Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==
    /\ l.event = "<"
    /\ l.pkt.msg.type = "pl"
    /\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==
    /\ l.event = "d"
    /\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==
    /\ l.event \in {"<", ">"}
    /\ l.pkt.msg.type = "trm"
    /\ \A n \in Node: ~active[n]
    /\ UNCHANGED vars

TraceNextConstraint ==
    LET i == TLCGet("level")
    IN /\ i <= Len(TraceLog)
       /\ LET logline == TraceLog[i]
          IN BP::
             /\ \/ IsInitiateToken(logline)
                \/ IsPassToken(logline)
                \/ IsRecvToken(logline)
                \/ IsSendMsg(logline)
                \/ IsRecvMsg(logline)
                \/ IsDeactivate(logline)
                \/ IsTrm(logline)
                /\ "failure" \notin DOMAIN logline

TraceInv ==
    LET l == TraceLog[TLCGet("level")] IN
    /\ "failure" \notin DOMAIN l
    /\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm") => \A n \in Node: ~active[n]

TraceView ==
    <<vars, TLCGet("level")>>

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", TraceLog[d],
                  "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

TraceAlias ==
    [
        log     |-> <<TLCGet("level"), TraceLog[TLCGet("level") - 1]>>,
        active  |-> active,
        color   |-> color,
        counter |-> counter,
        inbox   |-> inbox,
        term    |-> <<EWD998!terminationDetected, "=>", EWD998!Termination>>,
        enabled |-> [
            InitToken  |-> ENABLED InitiateProbe,
            PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
            SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
            RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
            Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
        ]
    ]

====