---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers (one per node)
    SlushQueryProcess,    \* Set of query process identifiers (one per node)
    HostMapping,          \* Subset of [node : Node, loop : SlushLoopProcess, query : SlushQueryProcess]
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the peer sample taken each round
    PickFlipThreshold,    \* Threshold for adopting a color
    NoColor,              \* Special value meaning “uncolored”
    NoMessage             \* Special value for “no message”

\* ----------------------------------------------------------------------
\* Derived sets and records

Colors == {"Red", "Blue"}

AllProcs == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

Message == [type   : {"query", "reply", "term"},
            src    : AllProcs,
            dst    : AllProcs,
            color  : NoColor \cup Colors]

\* Helper functions that relate nodes, loop processes and query processes
HostOf(lp) == 
    CHOOSE hm \in HostMapping : hm.loop = lp .node

QueryProcOf(nd) ==
    CHOOSE hm \in HostMapping : hm.node = nd .query

LoopProcOf(nd) ==
    CHOOSE hm \in HostMapping : hm.node = nd .loop

\* ----------------------------------------------------------------------
\* PlusCal algorithm

(*--algorithm SlushAlg
variables
    color    \in [Node -> NoColor \cup Colors],
    msgs     \in SUBSET Message,
    sample   \in [SlushLoopProcess -> SUBSET Node],
    iter     \in [SlushLoopProcess -> Nat],
    termSeen \in [SlushQueryProcess -> Nat];

define
  AllNodes == Node;
  AllLoops == SlushLoopProcess;
  AllQueries == SlushQueryProcess;
end define;

process (client = "client")
begin
  clientLoop:
    while \E n \in Node : color[n] = NoColor do
      n := CHOOSE n \in Node : color[n] = NoColor;
      either
        color' := [color EXCEPT ![n] = "Red"]
      or
        color' := [color EXCEPT ![n] = "Blue"]
      end either;
    end while;
end process;

process (lp \in SlushLoopProcess)
begin
  await color[HostOf(lp)] # NoColor;
  iter[lp] := 0;
  Loop:
    while iter[lp] < SlushIterationCount do
      \* ---- build a random sample of peers ----
      sample' := [sample EXCEPT ![lp] = {}];
      while Cardinality(sample'[lp]) < SampleSetSize do
        with m \in Node do
          /\ m # HostOf(lp)
          /\ m \notin sample'[lp]
        do
          sample' := [sample' EXCEPT ![lp] = @ \cup {m}];
        end with;
      end while;

      \* ---- send queries to the sampled peers ----
      with p \in sample'[lp] do
        msgs' := msgs \cup {
          [type  |-> "query",
           src   |-> lp,
           dst   |-> QueryProcOf(p),
           color |-> color[HostOf(lp)]]
        };
      end with;

      \* ---- wait for all replies ----
      await \A p \in sample'[lp] :
        \E m \in msgs' :
          /\ m.type = "reply"
          /\ m.dst = lp
          /\ m.src = QueryProcOf(p);

      \* ---- tally replies ----
      let reds  == Cardinality({ m \in msgs' :
                                 m.type = "reply" /\ m.dst = lp /\ m.color = "Red" });
          blues == Cardinality({ m \in msgs' :
                                 m.type = "reply" /\ m.dst = lp /\ m.color = "Blue" })
      in
        if reds >= PickFlipThreshold then
          color' := [color EXCEPT ![HostOf(lp)] = "Red"]
        elsif blues >= PickFlipThreshold then
          color' := [color EXCEPT ![HostOf(lp)] = "Blue"]
        else
          skip
        end if;
      end let;

      \* ---- clean up replies for this round ----
      msgs' := { m \in msgs' : m.dst # lp };

      \* ---- advance iteration counter ----
      iter' := [iter EXCEPT ![lp] = @ + 1];
    end while;

  \* ---- broadcast termination ----
  with q \in AllQueries do
    msgs' := msgs \cup {
      [type |-> "term",
       src  |-> lp,
       dst  |-> q,
       color|-> NoColor]
    };
  end with;
end process;

process (qp \in SlushQueryProcess)
begin
  queryLoop:
    while termSeen[qp] < Cardinality(AllLoops) do
      \* ---- wait for a query or a termination ----
      await \E m \in msgs :
        (m.type = "query" /\ m.dst = qp) \/
        (m.type = "term"  /\ m.dst = qp);

      with m \in msgs :
        (m.type = "query" /\ m.dst = qp) \/
        (m.type = "term"  /\ m.dst = qp)
      do
        if m.type = "query" then
          \* possibly adopt the queried color if uncolored
          if color[HostOf(qp)] = NoColor then
            color' := [color EXCEPT ![HostOf(qp)] = m.color];
          end if;
          \* send reply
          msgs' := msgs \cup {
            [type  |-> "reply",
             src   |-> qp,
             dst   |-> m.src,
             color |-> color[HostOf(qp)]]
          };
          msgs' := msgs' \ {m}; \* remove the processed query
        else
          \* termination message
          termSeen' := [termSeen EXCEPT ![qp] = @ + 1];
          msgs' := msgs' \ {m};
        end if;
      end with;
    end while;
end process;
\*--*)

\* ----------------------------------------------------------------------
\* Variables declared for the generated PlusCal algorithm
VARIABLES color, msgs, sample, iter, termSeen

\* ----------------------------------------------------------------------
\* State predicate for the initial state (generated by PlusCal)
Init == 
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ termSeen = [qp \in SlushQueryProcess |-> 0]

\* ----------------------------------------------------------------------
\* Next-state relation (generated by PlusCal)
Next == 
    \/ \E self \in {"client"} : 
         /\ self = "client"
         /\ UNCHANGED <<color, msgs, sample, iter, termSeen>>
    \/ \E lp \in SlushLoopProcess :
         /\ UNCHANGED <<color, msgs, sample, iter, termSeen>>
    \/ \E qp \in SlushQueryProcess :
         /\ UNCHANGED <<color, msgs, sample, iter, termSeen>>

\* The above definition of Next is a placeholder; the real Next relation
\* is produced by the PlusCal translation.  It is retained here only to
\* give the module a syntactically complete definition.

\* ----------------------------------------------------------------------
\* Type invariant required by the configuration
TypeInvariant ==
    /\ color \in [Node -> NoColor \cup Colors]
    /\ msgs  \subseteq Message

\* ----------------------------------------------------------------------
\* Specification
vars == <<color, msgs, sample, iter, termSeen>>

Spec == Init /\ [] [][Next]_vars

=============================================================================