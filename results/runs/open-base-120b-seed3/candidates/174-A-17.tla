---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

(* two possible colors *)
Red  == "Red"
Blue == "Blue"
Colors == {Red, Blue}

(* helper operators to relate nodes and processes via HostMapping *)
LoopNode(lp)  == CHOOSE n \in Node : <<n, lp, q>> \in HostMapping
QueryNode(qp) == CHOOSE n \in Node : <<n, l, qp>> \in HostMapping
QueryOfNode(n) == CHOOSE qp \in SlushQueryProcess : <<n, l, qp>> \in HostMapping
SamplePeers(lp) == { QueryOfNode(n) : n \in Node \ {LoopNode(lp)} }

(*--algorithm SlushAlg
variables
    col      = [n \in Node |-> NoColor],
    msgs     = {},
    iter     = [lp \in SlushLoopProcess |-> 0],
    doneLoop = {},
    doneQuery= {};

process (client = "client")
begin
  Client:
    while \E n \in Node : col[n] = NoColor do
      with n \in { n \in Node : col[n] = NoColor } do
        with c \in Colors do
          col := [col EXCEPT ![n] = c];
        end with;
      end with;
    end while;
end process;

process (lp \in SlushLoopProcess)
variables sample = {}
begin
  WaitColor:
    while col[LoopNode(lp)] = NoColor do
      skip;
    end while;
  LoopIter:
    while iter[lp] < SlushIterationCount do
      \* choose a sample set of peers
      sample := CHOOSE s \in SUBSET SamplePeers(lp) :
                  Cardinality(s) = SampleSetSize;
      \* send a query to each sampled peer
      with peer \in sample do
        msgs := msgs \cup {
          [kind  |-> "Query",
           src   |-> lp,
           dst   |-> peer,
           color |-> col[LoopNode(lp)] ]
        };
      end with;
      \* wait until replies from all sampled peers have arrived
      while Cardinality(
                { m \in msgs :
                    /\ m.kind = "Reply"
                    /\ m.dst  = lp })
            < SampleSetSize
        do
          skip;
        end while;
      \* tally replies
      with replies == { m \in msgs :
                         /\ m.kind = "Reply"
                         /\ m.dst  = lp } do
        let reds  == Cardinality({ m \in replies : m.color = Red });
            blues == Cardinality({ m \in replies : m.color = Blue })
        in
          if reds >= PickFlipThreshold then
            col := [col EXCEPT ![LoopNode(lp)] = Red];
          elsif blues >= PickFlipThreshold then
            col := [col EXCEPT ![LoopNode(lp)] = Blue];
          else
            skip;
          end if;
      end with;
      \* clean up messages of this round
      msgs := { m \in msgs :
                ~(/\ m.kind = "Query" /\ m.src = lp/)
                /\ ~(/\ m.kind = "Reply" /\ m.dst = lp/) };
      iter[lp] := iter[lp] + 1;
    end while;
  \* broadcast termination to all loop processes
  with p \in SlushLoopProcess do
    msgs := msgs \cup {
      [kind |-> "Terminate",
       src  |-> lp,
       dst  |-> p]
    };
  end with;
  doneLoop := doneLoop \cup {lp};
end process;

process (qp \in SlushQueryProcess)
begin
  QueryLoop:
    while doneLoop # SlushLoopProcess do
      either
        \* handle an incoming query
        with m \in msgs :
          /\ m.kind = "Query"
          /\ m.dst  = qp
        do
          if col[QueryNode(qp)] = NoColor then
            col := [col EXCEPT ![QueryNode(qp)] = m.color];
          end if;
          msgs := msgs \cup {
            [kind  |-> "Reply",
             src   |-> qp,
             dst   |-> m.src,
             color |-> col[QueryNode(qp)]]
          };
          msgs := msgs \ {m};
        end with;
      or
        \* no query to handle now
        skip;
      end either;
    end while;
  doneQuery := doneQuery \cup {qp};
end process;
end algorithm; *)

Spec == Init /\ [] [Next]_vars

TypeInvariant ==
    /\ col \in [Node -> (NoColor \cup Colors)]
    /\ msgs \subseteq
        [kind  : {"Query","Reply","Terminate"},
         src   : (SlushLoopProcess \cup SlushQueryProcess),
         dst   : (SlushLoopProcess \cup SlushQueryProcess),
         color : (Colors \cup {NoColor})]

====