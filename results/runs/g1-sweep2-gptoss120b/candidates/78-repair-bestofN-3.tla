---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* Trace validation has been designed for TLC running in default model-checking
 \* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

JsonLog ==
    \* Deserialize the System log as a sequence of records from the log file.
     \* Run TLC with (assuming a suitable "tlc" shell alias):
     \* $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
     \* Fall back to trace.ndjson if the JSON environment variable is not set.
    ndJsonDeserialize(
        IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
        ELSE "specifications/ewd998/EWD998ChanTrace.ndjson"
    )

\* The number of nodes is obtained from the environment (or defaults to 0).
\* This avoids the use of ndJsonDeserialize in a constant definition, which
\* would trigger an unbounded CHOOSE during constant substitution.
TraceN ==
    IF "N" \in DOMAIN IOEnv THEN
        IOEnv.N
    ELSE
        0

TraceLog ==
    \* The first line of the log statement has the number of nodes.
    \* (The N value itself is supplied via the constant N, which is set to TraceN
    \* by the configuration file.)
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
        LAMBDA vc : DOMAIN vc
    )

-----------------------------------------------------------------------------

TraceInit ==
    /\ Init!1
    /\ Init!2
    \* We happen to know that in the implementation all nodes are initially empty and white.
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]

TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
     \* equivalent to the (canonical) Spec formual  Init /\ [][Next]_vars  .  
     \* However, TLC's breadth-first algorithm does not explore successor
     \* states of a *seen* state.  Since one or more states may appear one or 
     \* more times in the the trace, the  UNCHANGED vars  combined with the
     \*  TraceView  that includes  TLCGet("level")  is our workaround. 
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

-----------------------------------------------------------------------------

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
    /\ l.pkt.msg .type = "pl"
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

TraceNextConstraint ==
    \* We could have used an auxiliary spec variable for i  , but TLCGet("level") has the
     \* advantage that TLC continues to show the high-level action names instead of just  Next.
     \* However, it is imparative to run TLC with the TraceView above configured as a VIEW in
     \* TLC's config file.  Otherwise, TLC will stop model checking when a high-level state
     \* appears a second time in the trace.
    LET i == TLCGet("level")
    IN \* Equals FALSE if we get past the end of the log, causing model checking to stop.
       /\ i <= Len(TraceLog)
       /\ LET logline == TraceLog[i]
          IN \* If the postcondition  TraceAccepted  is violated, adding a TLA+ debugger
              \* breakpoint with a hit count copied from TLC's error message on the 
              \* BP:: line below is the first step towards diagnosing a divergence. Once
              \* hit, advance evaluation with step over (F10) and step into (F11).
              BP::
              /\ \/ IsInitiateToken(logline)
                 \/ IsPassToken(logline)
                 \/ IsRecvToken(logline)
                 \/ IsSendMsg(logline)
                 \/ IsRecvMsg(logline)
                 \/ IsDeactivate(logline)
                 \/ IsTrm(logline)
              \* Fail trace validation if the log contains a failure message. As an alternative,
               \* we could have used  TraceInv below, which would cause TLC to print the current
               \* trace upon its violation.  For the sake of consistency, we use the 
               \*  TraceAccepted  approach for all trace validation.
              /\ "failure" \notin DOMAIN logline

TraceInv ==
    LET l == TraceLog[TLCGet("level")] IN
    /\ "failure" \notin DOMAIN l
    /\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm") => \A n \in Node: ~active[n]

-----------------------------------------------------------------------------

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<vars, TLCGet("level")>>

-----------------------------------------------------------------------------

TraceAccepted ==
    \* If the prefix of the TLA+ behavior is shorter than the trace, TLC will
     \* report a violation of this postcondition.  But why do we need a postcondition
     \* at all?  Couldn't we use an ordinary property such as
     \*  <>[](TLCGet("level") >= Len(TraceLog))  ?  The answer is that an ordinary
     \* property is true of a single behavior, whereas  TraceAccepted  is true of a
     \* set of behaviors; it is essentially a poor man's hyperproperty.
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(
            << "Failed matching the trace to (a prefix of) a behavior:",
               TraceLog[d],
               "TLA+ debugger breakpoint hit count " \o ToString(d+1) >>,
            FALSE)

-----------------------------------------------------------------------------

TraceAlias ==
    \* The  TraceAlias  is nothing but a debugging aid.  Especially the enabled
     \* helped me figure out why a trace was not accepted.  In the TLA+ debugger,
     \* this  TraceAlias  can be entered as a "WATCH" expression.
    [
        \* TODO: Funny TLCGet("level")-1 could be removed if the spec has an
        \* TODO: auxiliary counter variable  i  .  Would also take care of 
        \* TODO: the bug that TLCGet("level")-1 is not defined for the initial
        \* TODO: state.
        log     |-> << TLCGet("level"), TraceLog[TLCGet("level") - 1] >>,
        active  |-> active,
        color   |-> color,
        counter |-> counter,
        inbox   |-> inbox,
        term    |-> << EWD998!terminationDetected, "=>", EWD998!Termination >>,
        enabled |-> 
            [
                InitToken  |-> ENABLED InitiateProbe,
                PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
                SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
                RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
                Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
            ]
    ]

=============================================================================