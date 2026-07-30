---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
ASSUME Cardinality(Node) = Cardinality(SlushQueryProcess)

\* Message types: QueryMsg (a loop process asks a query process for its color),
\* ReplyMsg (the query process replies), and TermMsg (a loop process is done).
Message == [from : SlushLoopProcess, to : SlushQueryProcess, kind : {"QueryMsg", "ReplyMsg"}, payload : NoColor \cup {1, 2}]
        \cup [from : SlushLoopProcess, kind : {"TermMsg"}]

Color == {NoColor, 1, 2}
ProcessState == {"Idle", "Waiting", "Replying", "Done"}

VARIABLES atMostOnce, inbox, pc, sample, itersCompleted

vars == <<atMostOnce, inbox, pc, sample, itersCompleted>>

\* atMostOnce tracks each node's current color (or NoColor) and is written by
\* the client process, by query processes on behalf of the host node, and by
\* loop processes when a flip threshold is reached.
Init ==
  /\ atMostOnce = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [lp \in SlushLoopProcess |-> "Idle"]
        \cup [qp \in SlushQueryProcess |-> "Replying"]
        \cup [p \in {"client"} |-> "Ready"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ itersCompleted = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node, modeling an
\* external transaction arriving at the network.
AssignColor ==
  /\ pc["client"] = "Ready"
  /\ \E n \in Node :
       /\ atMostOnce[n] = NoColor
       /\ \E c \in {1, 2} : atMostOnce' = [atMostOnce EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "Done"]
  /\ UNCHANGED <<inbox, sample, itersCompleted>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "Idle"
       /\ \E n \in Node :
            /\ <<n, lp, "loop">> \in HostMapping
            /\ atMostOnce[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "Waiting"]
  /\ UNCHANGED <<atMostOnce, inbox, sample, itersCompleted>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "Waiting"
       /\ \E s \in SUBSET SlushQueryProcess :
            /\ Cardinality(s) = SampleSetSize
            /\ inbox' = inbox \cup
                 {[from |-> lp, to |-> qp, kind |-> "QueryMsg", payload |-> atMostOnce[
                      CHOOSE n \in Node : <<n, lp, "loop">> \in HostMapping]} : qp \in s]
            /\ sample' = [sample EXCEPT ![lp] = s]
  /\ UNCHANGED <<atMostOnce, pc, itersCompleted>>

\* A query process may answer a query and, if its host is uncolored, adopt
\* the incoming color itself. Slush messages travel over an asynchronous bus,
\* so replies are collected as they arrive in no particular order.
RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "QueryMsg"
       /\ \E n \in Node :
            /\ <<n, m.to, "query">> \in HostMapping
            /\ atMostOnce' = IF atMostOnce[n] = NoColor
                 THEN [atMostOnce EXCEPT ![n] = m.payload]
                 ELSE atMostOnce
            /\ inbox' = (inbox \ {m})
                 \cup {[from |-> m.from, to |-> m.to, kind |-> "ReplyMsg", payload |-> atMostOnce[n]]}
  /\ UNCHANGED <<pc, sample, itersCompleted>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "Waiting"
       /\ \A qp \in sample[lp] : [from |-> lp, to |-> qp, kind |-> "ReplyMsg"] \in inbox
       /\ inbox' = inbox \ {[m \in inbox : m.from = lp /\ m.kind = "ReplyMsg"]}
       /\ \E c \in {1, 2} :
            /\ Cardinality({m \in inbox : m.from = lp /\ m.kind = "ReplyMsg" /\ m.payload = c}) >= PickFlipThreshold
            /\ atMostOnce' = [n \in Node |-> IF <<n, lp, "loop">> \in HostMapping THEN c ELSE atMostOnce[n]]
       /\ sample' = [sample EXCEPT ![lp] = {}]
       /\ itersCompleted' = [itersCompleted EXCEPT ![lp] =
            IF itersCompleted[lp] < SlushIterationCount THEN itersCompleted[lp] + 1 ELSE itersCompleted[lp]]
       /\ pc' = [pc EXCEPT ![lp] = IF itersCompleted[lp] + 1 >= SlushIterationCount THEN "Done"
            ELSE "Waiting"]

LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "Done"
       /\ \A m \in inbox : m.kind # "ReplyMsg" \/ m.from # lp
       /\ inbox' = inbox \cup {[from |-> lp, kind |-> "TermMsg"]}
  /\ UNCHANGED <<atMostOnce, pc, sample, itersCompleted>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "Replying"
       /\ \A lp \in SlushLoopProcess : [from |-> lp, kind |-> "TermMsg"] \in inbox
       /\ pc' = [pc EXCEPT ![qp] = "Done"]
  /\ UNCHANGED <<atMostOnce, inbox, sample, itersCompleted>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

\* Both type checks are structural: colors are always legit values, and every
\* hop in the message bus carries a recognized kind.
TypeInvariant ==
  /\ \A n \in Node : atMostOnce[n] \in Color
  /\ \A m \in inbox :
       \/ m.kind = "TermMsg"
       \/ \E qp \in SlushQueryProcess : m.kind \in {"QueryMsg", "ReplyMsg"} /\ m.to = qp

====