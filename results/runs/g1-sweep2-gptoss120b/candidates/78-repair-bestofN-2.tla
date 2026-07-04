---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* Trace validation has been designed for TLC running in default model-checking
\* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

\* ----------------------------------------------------------------------
\* JSON log handling
\* ----------------------------------------------------------------------
JsonLog ==
    \* Deserialize the System log as a sequence of records from the log file.
    \* Run TLC with (assuming a suitable "tlc" shell alias):
    \* $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
    \* Fall back to trace.ndjson if the JSON environment variable is not set.
    ndJsonDeserialize(
        IF "JSON" \in DOMAIN IOEnv
        THEN IOEnv.JSON
        ELSE "specifications/ewd998/EWD998ChanTrace.ndjson"
    )

\* NOTE:
\* The constant N required by the configuration file must be a *constant*
\* expression.  The original definition of TraceN depended on JSON parsing,
\* which internally uses an unbounded CHOOSE and therefore cannot be used as a
\* constant substitution.  We replace it by a dummy constant (0) that will be
\* constrained to the actual value from the log in the initial state.
TraceN == 0

TraceLog ==
    \* The first line of the log statement has the number of nodes.
    \* SubSeq starting at 2 to skip the N value.
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    \* The JsonLog/Trace has been compiled out of several logs, collected from the
    \* nodes of the distributed system, and, thus, are unordered.
    IN CausalOrder(
          suffix,
          LAMBDA l : l.pkt.vc,
          \* ToString is a hack to work around the fact that the Json
          \* module deserializes {"0": 42, "1": 23} into the record
          \* [ 0 |-> 42, 1 |-> 23 ] with domain {"0","1"} and not into
          \* a function with domain {0, 1}.  This is a known issue of
          \* the Json module. Consider switching to, e.g., EDN
          \* (https://github.com/edn-format/edn).
          LAMBDA l : ToString(l.node),
          LAMBDA vc : DOMAIN vc)

\* ----------------------------------------------------------------------
\* Initial state (including tying the constant N to the value from the log)
\* ----------------------------------------------------------------------
TraceInit ==
    /\ Init!1
    /\ Init!2
    \* We happen to know that in the implementation all nodes are initially empty and white.
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]
    \* Constrain the constant N (supplied via the config file) to match the value
    \* recorded in the first line of the JSON log.
    /\ N = JsonLog[1].N

TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
    \* equivalent to the (canonical) Spec formual  Init /\ [][Next]_vars  .
    \* However, TLC's breadth-first algorithm does not explore successor
    \* states of a *seen* state.  Since one or more states may appear one or
    \* more times in the the trace, the  UNCHANGED vars  combined with the
    \*  TraceView  that includes  TLCGet("level")  is our workaround.
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

PayloadPred(msg) ==
    msg.type = "pl"

\* Beware to only prime e.g. inbox in inbox'[rcv] and *not* also rcv, i.e.,
\* inbox[rcv]'.  rcv is defined in terms of TLCGet("level") that correctly
\* handles priming, which causes for rcv' to equal rcv of the next log line.

IsInitiateToken(l) ==
    \* Log statement was printed by the sender (initiator).
    /\ l.event = ">"
    \* Log statement is about a token message.
    /\ l.pkt.msg.type = "tok"
    \* Log statement show N-1 to be receiver and 0 to be the sender.
    /\ l.pkt.rcv = N - 1
    /\ l.pkt.snd = 0
    /\ <<InitiateProbe>>_vars

IsPassToken(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    \* Log statement is about a token message.
    /\ l.pkt.msg.type = "tok"
    /\ LET snd == l.pkt.snd IN
        \* The high-level spec precludes the initiator from passing the token in the
        \* the  System  formula by remove the initiator from the set of all nodes.  Here,
        \* we model this by requiring that the sender is not the initiator.
        /\ l.pkt.snd > 0
        /\ <<PassToken(snd)>>_vars

\* Note that there is no corresponding sub-action in the high-level spec!  This constraint
\* is true of any sub-action that appends a tok message to the receiver's inbox.
IsRecvToken(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "<"
    /\ LET msg == l.pkt.msg
           rcv == l.pkt.rcv IN
        \* Log statement is about a token message.
        /\ msg.type = "tok"
        \* The number of payload messages in the node's inbox do not change.
        /\ \A n \in Node:
                SelectSeq(inbox[n], PayloadPred) = SelectSeq(inbox'[n], PayloadPred)
        \* The receivers's inbox contains a tok message in the next state.
        /\ \E idx \in DOMAIN inbox'[rcv]:
            /\ inbox'[rcv][idx].type = "tok"
            /\ inbox'[rcv][idx].q = msg.q
            /\ inbox'[rcv][idx].color = msg.color
        /\ UNCHANGED <<active, counter, color>>

IsSendMsg(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    \* Log statement is about a payload message.
    /\ l.pkt.msg.type = "pl"
    /\ <<SendMsg(l.pkt.snd)>>_vars
    /\ LET rcv == l.pkt.rcv IN
        \* The sender's inbox remains unchanged, but the receivers's inbox contains one more
        \* pl message.  In the implementation, the message is obviously in flight, i.e. it
        \* is send via the wire to the receiver.  However, the  SendMsg  action models it
        \* such that the message is atomically appended to the receiver's inbox.
        Len(SelectSeq(inbox[rcv], PayloadPred)) < Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "<"
    /\ l.pkt.msg.type = "pl"
    /\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "d"
    /\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==
    \* "trm" messages are not part of EWD998, and, thus, not modeled in EWD998Chan.  We map
    \* "trm" messages to (finite) stuttering, essentially, skipping the "trm" messages in
    \* the log.  One could have also preprocessed/filtered the trace log, but the extra
    \* step is not necessary.
    /\ l.event \in {"<", ">"}
    /\ l.pkt.msg.type = "trm"
    \* The (mere) existance of a "trm" message implies that *all* nodes have terminated.
    /\ \A n \in Node: ~active[n]
    \* Careful! Without UNCHANGED vars, isTrm is true of all states of the high-level spec
    \* if the current line is a trm message.  In general, it is good practice to constrain
    \* all spec variables!
    /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Trace driving constraints
\* ----------------------------------------------------------------------
TraceNextConstraint ==
    \* We could have used an auxiliary spec variable for i , but TLCGet("level") has the
    \* advantage that TLC continues to show the high-level action names instead of just  Next.
    \* However, it is imparative to run TLC with the TraceView above configured as a VIEW in
    \* TLC's config file.  Otherwise, TLC will stop model checking when a high-level state
    \* appears a second time in the trace.
    LET i == TLCGet("level")
    IN /\ i <= Len(TraceLog)
       /\ LET logline == TraceLog[i]
          IN BP:: /\ \/ IsInitiateToken(logline)
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

\* ----------------------------------------------------------------------
\* TLC view to avoid state merging
\* ----------------------------------------------------------------------
TraceView ==
    <<vars, TLCGet("level")>>

\* ----------------------------------------------------------------------
\* Acceptance condition
\* ----------------------------------------------------------------------
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:",
                TraceLog[d],
                "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

\* ----------------------------------------------------------------------
\* Debugging alias
\* ----------------------------------------------------------------------
TraceAlias ==
    [
        \* TODO: Funny TLCGet("level")-1 could be removed if the spec has an
        \* TODO: auxiliary counter variable  i  .  Would also take care of 
        \* TODO: the bug that TLCGet("level")-1 is not defined for the initial
        \* TODO: state.
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

=============================================================================