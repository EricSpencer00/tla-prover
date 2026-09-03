---- MODULE Nano ----
EXTENDS Naturals, Sequences

(* A TLA+ spec modeling Nano's block-lattice protocol: each account has its own   *)
(* chain of blocks, and a block records its previous block (or both previous and  *)
(* source in the case of a receive block).  This spec focuses on the hash and      *)
(* signature aspects of the protocol and models the block creation and           *)
(* validation steps.  The block-identifier set is finite, so the ledger's         *)
(* replicated copies are bounded, which is what makes model checking feasible.    *)

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

(* A node's local copy of the distributed ledger: block hash -> block, or NoBlock.
   Every node keeps its own copy, which is how the network tolerates latency.      *)
Ledger == [Hash -> ("sent" \cup "receive" \cup "open" \cup "change") \X PublicKey \X Hash \X (0 .. GenesisBalance)]

VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

TypeOK ==
  /\ lastHash \in {"sent", "receive", "open", "change", NoHash}
  /\ ledger \in [Node -> Ledger]
  /\ received \in [Node -> SUBSET Ledger]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* Account-chain balance: walk the chain backwards and sum the values.
RECURSIVE ChainBalance(_, _)
ChainBalance(node, hsh) ==
  IF hsh = NoHash
    THEN 0
    ELSE LET blk == ledger[node][hsh] IN
         IF blk = NoBlock
           THEN 0
           ELSE (IF blk[1] = "sent"
                   THEN -blk[4]
                   ELSE IF blk[1] = "receive"
                     THEN blk[4]
                     ELSE 0)
                + ChainBalance(node, blk[3])

BalanceOf(node) == ChainBalance(node, lastHash)

\* The whole point: a node must be able to verify a signature against the
\* account's own public key (the chain determines the account, not a label).
ValidSignature(node, blk) == blk[2] = node

\* A network node broadcasts a newly created block to every other node's
\* received-set (in-flight blocks that are yet to be validated).
BroadcastBlock(newblk) == [n \in Node |-> received[n] \cup {newblk}]

CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E pk \in PrivateKey :
       /\ \E h \in Hash :
            /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = << "sent", pk, NoHash, GenesisBalance >>]]
            /\ lastHash' = h
            /\ received' = BroadcastBlock(<< "sent", pk, NoHash, GenesisBalance >>)
  /\ UNCHANGED << >>

CreateSendBlock ==
  /\ \E node \in Node :
       /\ BalanceOf(node) > 0
       /\ \E recipient \in PublicKey :
            /\ \E amt \in 1 .. BalanceOf(node) :
                 /\ \E h \in Hash :
                      /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = << "sent", node, lastHash, amt >>]]
                      /\ lastHash' = h
                      /\ received' = BroadcastBlock(<< "sent", node, lastHash, amt >>)
  /\ UNCHANGED << >>

CreateOpenBlock ==
  /\ \E node \in Node :
       /\ \E src \in Hash :
            /\ \E h \in Hash :
                 /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = << "open", node, src, 0 >>]]
                 /\ lastHash' = h
                 /\ received' = BroadcastBlock(<< "open", node, src, 0 >>)
  /\ UNCHANGED << >>

CreateReceiveBlock ==
  /\ \E node \in Node :
       /\ \E src \in Hash :
            /\ \E amt \in 1 .. GenesisBalance :
                 /\ \E h \in Hash :
                      /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = << "receive", node, src, amt >>]]
                      /\ lastHash' = h
                      /\ received' = BroadcastBlock(<< "receive", node, src, amt >>)
  /\ UNCHANGED << >>

CreateChangeRepresentative ==
  /\ \E node \in Node :
       /\ \E h \in Hash :
            /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = << "change", node, lastHash, 0 >>]]
            /\ lastHash' = h
            /\ received' = BroadcastBlock(<< "change", node, lastHash, 0 >>)
  /\ UNCHANGED << >>

ValidateBlock ==
  /\ \E node \in Node :
       /\ \E blk \in received[node] :
            /\ ValidSignature(node, blk)
            /\ ledger' = [ledger EXCEPT ![node] = @ \cup {blk}]
            /\ received' = [received EXCEPT ![node] = @ \ {blk}]
  /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
  \/ CreateReceiveBlock \/ CreateChangeRepresentative \/ ValidateBlock

Spec == Init /\ [][Next]_vars

(* Every block in every node's ledger has a signature that matches that node's *)
(* public key (the account that owns the chain it's on).                         *)
SafetyInvariant == \A node \in Node : \A h \in Hash : ledger[node][h] # NoBlock => ledger[node][h][2] = node

TypeInvariant == TypeOK

====