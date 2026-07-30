---- MODULE Slush ----
EXTENDS Integers, FiniteSets

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

ASSUME /\ NoColor \notin Node
        /\ NoMessage \notin Node

\* Two colors for Slush, plus an uncolored state.
Color == Node \cup {NoColor}

MsgKind == {"query", "reply", "term"}

VARIABLES color, msgs, pc, sample, iterations

vars == <<color, msgs, pc, sample, iterations>>

TypeOK ==
  /\ color \in [Node -> Color]
  /\ msgs \subseteq [kind: MsgKind, src: Node, dst: Node, payload: Color]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} -> Nat]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client process is implicit; all it does is hand nodes their first color.
AssignColor(n, c) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, iterations>>

RequireColor(p) ==
  /\ pc[p] = 0
  /\ \/ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, msgs, sample, iterations>>

QueryPeers(p, s) ==
  /\ pc[p] = 1
  /\ cardinality(s) = SampleSetSize
  /\ \A m \in s : <<p, m>> \in HostMapping
  /\ LET n == CHOOSE q \in Node : <<p, q>> \in HostMapping IN
       /\ \A m \in s : msgs' = msgs \cup {[kind |-> "query", src |-> n, dst |-> m, payload |-> color[n]]}
     /\ sample' = [sample EXCEPT ![p] = s]
  /\ UNCHANGED <<color, pc, iterations>>

\* Reply: adopt the query's color if still uncolored, then send back own color.
RespondQuery(m) ==
  /\ \E q \in SlushLoopProcess :
       /\ \E Q \in msgs :
            /\ Q.kind = "query" /\ Q.dst = m /\ Q.payload \in Node
            /\ color[Q.dst] = NoColor
            /\ color' = [color EXCEPT ![Q.dst] = Q.payload]
            /\ msgs' = (msgs \ {Q}) \cup {[kind |-> "reply", src |-> Q.dst, dst |-> Q.src, payload |-> Q.payload]}
  /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies(p) ==
  /\ pc[p] = 1
  /\ sample[p] # {}
  /\ \A n \in sample[p] :
       \E R \in msgs :
         /\ R.kind = "reply" /\ R.dst = n /\ R.src \in sample[p]
  /\ LET n == CHOOSE q \in Node : <<p, q>> \in HostMapping IN
       /\ LET tally ==
            [color \in Node |-> Cardinality({R \in msgs : R.kind = "reply" /\ R.dst = n /\ R.payload = color})] IN
         /\ color' = [color EXCEPT ![n] = IF \E c \in Node : tally[c] >= PickFlipThreshold THEN CHOOSE c \in Node : tally[c] >= PickFlipThreshold ELSE color[n]]
  /\ msgs' = {R \in msgs : ~(R.kind = "reply" /\ R.dst \in sample[p])}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
  /\ pc' = IF iterations[p] + 1 >= SlushIterationCount THEN [pc EXCEPT ![p] = 2] ELSE [pc EXCEPT ![p] = 1]

LoopTerminate(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<color, msgs, sample, iterations>>

QueryExit(m) ==
  /\ pc[m] # 0
  /\ \A p \in SlushLoopProcess : pc[p] = 3
  /\ pc' = [pc EXCEPT ![m] = 3]
  /\ UNCHANGED <<color, msgs, sample, iterations>>

Next ==
  \/ \E n \in Node, c \in Node : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : \E s \in SUBSET Node : QueryPeers(p, s)
  \/ \E m \in SlushQueryProcess : RespondQuery(m)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ \E m \in SlushQueryProcess : QueryExit(m)

Spec == Init /\ [][Next]_vars

\* Once every process is done no action is enabled, so strong fairness here is
\* just a way of saying the spec eventually reaches that quiet end state.
AllDone ==
  /\ \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = 3
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
            /\ SF_vars(AllDone)

====