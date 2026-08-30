---- MODULE Slush ----
(* Slush: a metastable consensus protocol from the Avalanche family. Each
   node runs a loop process that repeatedly samples peers and adopts a
   majority color. Actions: client assigns colors, loops query peers,
   tally replies, and converge. TypeInvariant: color map and messages
   stay well typed; Termination: all processes eventually finish. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
          SampleSetSize, PickFlipThreshold, NoColor, NoMessage

MessageType == {NoMessage} \cup Node \times SlushQueryProcess \times {NoColor} \cup
                 Node \times SlushLoopProcess \times (Node \cup {NoColor}) \cup
                 Node \times {"term"}

PRHelper == {p \in HostMapping : p[1] = n}

VARIABLES color, inbox, pc, sample, iterations
vars == <<color, inbox, pc, sample, iterations>>

TypeInvariant ==
    /\ color \in [Node -> Node \cup {NoColor}]
    /\ inbox \subseteq MessageType
    /\ pc \in [SlushLoopProcess -> {"awaitColor", "querying", "tallying", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in SlushLoopProcess |-> "awaitColor"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iterations = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
    /\ \E n \in Node, c \in Node : color[n] = NoColor /\ color' = [color EXCEPT ![n] = c]
    \/ UNCHANGED <<inbox, pc, sample, iterations>>

RequireColor ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "awaitColor"
         /\ LET n == CHOOSE q \in HostMapping : q[1] = p /\ q[2] = "loop" @@ q[3] IN
              /\ color[n] # NoColor
              /\ pc' = [pc EXCEPT ![p] = "querying"]
    /\ UNCHANGED <<color, inbox, sample, iterations>>

QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "querying"
         /\ iterations[p] < SlushIterationCount
         /\ sample' = [sample EXCEPT ![p] = ChooseK(NodesExcept(p), SampleSetSize)]
         /\ LET n == CHOOSE q \in HostMapping : q[1] = p /\ q[2] = "loop" @@ q[3] IN
              inbox' = inbox \cup {<<n, m, color[n]>> : m \in sample[p]}
    /\ UNCHANGED <<color, pc, iterations>>

RespondToQuery ==
    /\ \E n \in Node, m \in SlushQueryProcess, e \in Node \cup {NoColor} :
         /\ <<n, m, e>> \in inbox
         /\ inbox' = inbox \ {<<n, m, e>>}
         /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = e] ELSE color
         /\ LET p == CHOOSE q \in HostMapping : q[1] = n /\ q[3] = m @@ q[2] IN
              inbox' = inbox' \cup {<<n, p, color[n]>>}
    /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "querying"
         /\ \E a \in Node, b \in Node :
              /\ <<a, p, b>> \in inbox
              /\ sample[p] \subseteq PRHelper
              /\ Cardinality(sample[p]) = SampleSetSize
              /\ Cardinality({q \in sample[p] : color[q] = b}) >= PickFlipThreshold
              /\ LET n == CHOOSE q \in HostMapping : q[1] = p /\ q[3] = "loop" @@ q[2] IN
                   color' = [color EXCEPT ![n] = b]
              /\ pc' = [pc EXCEPT ![p] = "tallying"]
              /\ inbox' = inbox \ {<<a, p, b>>}
    /\ UNCHANGED <<sample, iterations>>

LoopTermination ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "tallying"
         /\ iterations[p] + 1 = SlushIterationCount
         /\ pc' = [pc EXCEPT ![p] = "done"]
         /\ iterations' = [iterations EXCEPT ![p] = iterations[p] + 1]
         /\ inbox' = inbox \cup {<<CHOOSE q \in HostMapping : q[1] = p /\ q[3] = "loop" @@ q[2], "term", NoColor>>}
    /\ UNCHANGED <<color, sample>>

QueryLoopExit ==
    /\ \E m \in SlushQueryProcess :
         /\ \A p \in SlushLoopProcess : <<CHOOSE q \in HostMapping : q[2] = p /\ q[3] = "loop" @@ q[1], "term", NoColor>> \in inbox
         /\ pc' = [p \in SlushQueryProcess |-> "done"]
    /\ UNCHANGED <<color, inbox, sample, iterations>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit)

NodesExcept(p) == {n \in Node : n # CHOOSE q \in HostMapping : q[1] = p /\ q[2] = "loop" @@ q[3]}
ChooseK(S, k) == {x \in S : x \in CHOOSE X \in (SUBSET S) : Cardinality(X) = k : X}
Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"
====