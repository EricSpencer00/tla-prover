---- MODULE Slush ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Node,                \* set of node identifiers
  SlushLoopProcess,    \* set of loop process identifiers
  SlushQueryProcess,   \* set of query process identifiers
  HostMapping,         \* set of triples <<loop, query, node>>
  SlushIterationCount, \* number of iterations each loop performs
  SampleSetSize,       \* size of the peer sample
  PickFlipThreshold,   \* threshold for flipping color
  NoColor,             \* sentinel for an uncolored node
  NoMessage            \* sentinel for “no message” (unused but required)

CONSTANT Red, Blue      \* the two possible colors

ASSUME
  /\ Red # Blue
  /\ NoColor # Red
  /\ NoColor # Blue

(* -----------------------------------------------------------------
   Helper functions that map processes to their host node using the
   HostMapping constant.
   ----------------------------------------------------------------- *)
LoopNode(lp) == CHOOSE n \in Node : <<lp, _, n>> \in HostMapping
QueryNode(qp) == CHOOSE n \in Node : <<_, qp, n>> \in HostMapping

(* -----------------------------------------------------------------
   Message record definition.  All messages that appear in the system
   belong to this type.
   ----------------------------------------------------------------- *)
Message ==
  [ type : {"query", "reply", "term"},
    src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
    dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
    col  : {Red, Blue, NoColor} ]

(* -----------------------------------------------------------------
   PlusCal algorithm describing the behavior of the three kinds of
   processes: the client that initially colors nodes, the loop processes
   that execute the Slush iteration, and the query processes that answer
   queries.  The algorithm is intentionally deterministic apart from the
   nondeterministic choices required by the specification (e.g., picking
   a node to color or a sample of peers).
   ----------------------------------------------------------------- *)

(*--algorithm SlushAlg
variables
  color  = [n \in Node |-> NoColor],
  msgs   = {},
  sample = [lp \in SlushLoopProcess |-> {}],
  iter   = [lp \in SlushLoopProcess |-> 0];

process (client = "client")
begin
  clientLoop:
    while \E n \in Node : color[n] = NoColor do
      with n \in Node : color[n] = NoColor do
        with c \in {Red, Blue} do
          color := [color EXCEPT ![n] = c];
        end with;
      end with;
    end while;
end process;

process (lp \in SlushLoopProcess)
variables
  myNode = LoopNode(self);
begin
  awaitColor:
    while color[myNode] = NoColor do
      skip;
    end while;

  iteration:
    while iter[self] < SlushIterationCount do
      \* ----- sample a set of peers ---------------------------------
      sample[self] :=
        { q \in SlushQueryProcess :
            q # CHOOSE qp \in SlushQueryProcess :
                  <<_, qp, myNode>> \in HostMapping }
        \cap Subset(SlushQueryProcess, SampleSetSize);

      \* ----- send a query to each sampled peer --------------------
      with qp \in sample[self] do
        msgs := msgs \cup
          {[type |-> "query",
            src  |-> self,
            dst  |-> qp,
            col  |-> color[myNode]]};
      end with;

      \* ----- wait for all replies ---------------------------------
      with replies \in SUBSET msgs :
        /\ \A m \in replies :
              m.type = "reply" /\ m.dst = self /\ m.src \in sample[self]
        /\ Cardinality(replies) = SampleSetSize
      do
        reds  == Cardinality({ m \in replies : m.col = Red });
        blues == Cardinality({ m \in replies : m.col = Blue });

        if reds >= PickFlipThreshold then
          color := [color EXCEPT ![myNode] = Red];
        elsif blues >= PickFlipThreshold then
          color := [color EXCEPT ![myNode] = Blue];
        else
          skip;
        end if;

        msgs   := msgs \ replies;
        iter[self] := iter[self] + 1;
        sample[self] := {};
      end with;
    end while;

  \* ----- broadcast termination to all query processes ----------
  with qp \in SlushQueryProcess do
    msgs := msgs \cup
      {[type |-> "term",
        src  |-> self,
        dst  |-> qp,
        col  |-> NoColor]};
  end with;
end process;

process (qp \in SlushQueryProcess)
variables
  myNode = QueryNode(self);
begin
  queryLoop:
    while TRUE do
      either
        \* ----- receive a query ------------------------------------
        with m \in msgs :
          /\ m.type = "query"
          /\ m.dst = self
        do
          if color[myNode] = NoColor then
            color := [color EXCEPT ![myNode] = m.col];
          end if;

          msgs := (msgs \ {m}) \cup
            {[type |-> "reply",
              src  |-> self,
              dst  |-> m.src,
              col  |-> color[myNode]]};
        end with;

      or
        \* ----- receive a termination -------------------------------
        with m \in msgs :
          /\ m.type = "term"
          /\ m.dst = self
        do
          msgs := msgs \ {m};
          \* (Simplified) exit when all loop processes have sent a
          \* termination message; the actual exit condition is omitted
          \* because it does not affect the safety properties we check.
          skip;
        end with;
      end either;
    end while;
end process;
end algorithm;*)

Spec ==
  Init /\ [][Next]_(<<color, msgs, sample, iter>>)

TypeInvariant ==
  /\ color \in [Node -> {Red, Blue, NoColor}]
  /\ msgs  \subseteq Message
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iter   \in [SlushLoopProcess -> Nat]

====