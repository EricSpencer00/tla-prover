---- MODULE Nano ----
EXTENDS Naturals

(* System overview: a Nano-like blockchain using a block lattice, with the model
   focusing on hash functions and signatures.  Every account has its own chain
   of blocks, and block order is part of the state. *)
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* The hash operator is an abstract constant substituted by the .cfg; it takes
\* the block's data and the previous hash and yields a new hash.
VARIABLES lastHash, ledger, received

Vars == <<lastHash, ledger, received>>

\* A signed block: its author (public key), the previous block on the account
\* chain, the block type, and the block data (amount, recipient, or rep).
Block ==
  [author : PublicKey,
   previous : {NoHash} \cup Hash,
   kind : {"genesis", "send", "open", "receive", "change"},
   data : {NoBlockVal} \cup (Nat \cup PublicKey)]

\* The distributed ledger is replicated across every network node.
Ledger == [n \in Node |-> [h \in {NoHash} \cup Hash |-> Block \cup {NoBlockVal}]]

TypeOK ==
  /\ lastHash \in {NoHashVal} \cup Hash
  /\ ledger \in Ledger
  /\ received \in [n \in Node |-> SUBSET {NoHash} \cup Hash]

\* The sum of all account balances never exceeds the genesis balance.
\* It is defined separately from the main invariant.
RECURSIVE WalkChain(_)
WalkChain(h) ==
  IF h = NoHash THEN 0
  ELSE
    LET blk == CHOOSE b \in {NoHash} \cup Hash : ledger["n1"][b] # NoBlockVal /\ b = h
    IN IF blk.kind \in {"receive", "open"}
         THEN blk.data + WalkChain(blk.previous)
         ELSE WalkChain(blk.previous)

BalanceOK == WalkChain(NoHash) <= GenesisBalance

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in {NoHash} \cup Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesis(n, k) ==
  /\ lastHash = NoHashVal
  /\ k \in PrivateKey
  /\ LET blk == [author |-> k, previous |-> NoHash, kind |-> "genesis", data |-> GenesisBalance]
         nh == CalculateHash(blk, NoHash)
     IN /\ lastHash' = nh
        /\ ledger' = [node \in Node |-> [ledger[node] EXCEPT ![nh] = blk]]
        /\ received' = [n \in Node |-> {nh}]
  /\ UNCHANGED <<\E>>

CreateSend(n, k, amt, rec) ==
  /\ k \in PrivateKey
  /\ WalkChainNoHash(n) >= amt
  /\ lastHash # NoHashVal
  /\ LET blk == [author |-> k, previous |-> lastHash,
                 kind |-> "send", data |-> amt]
         nh == CalculateHash(blk, lastHash)
     IN /\ lastHash' = nh
        /\ ledger' = [node \in Node |-> [ledger[node] EXCEPT ![nh] = blk]]
        /\ received' = [node \in Node |-> {nh}]
  /\ UNCHANGED <<\E>>

CreateOpen(n, k, src) ==
  /\ k \in PrivateKey
  /\ lastHash # NoHashVal
  /\ LET blk == [author |-> k, previous |-> lastHash,
                 kind |-> "open", data |-> src]
         nh == CalculateHash(blk, lastHash)
     IN /\ lastHash' = nh
        /\ ledger' = [node \in Node |-> [ledger[node] EXCEPT ![nh] = blk]]
        /\ received' = [node \in Node |-> {nh}]
  /\ UNCHANGED <<\E>>

CreateReceive(n, k, src) ==
  /\ k \in PrivateKey
  /\ lastHash # NoHashVal
  /\ LET blk == [author |-> k, previous |-> lastHash,
                 kind |-> "receive", data |-> src]
         nh == CalculateHash(blk, lastHash)
     IN /\ lastHash' = nh
        /\ ledger' = [node \in Node |-> [ledger[node] EXCEPT ![nh] = blk]]
        /\ received' = [node \in Node |-> {nh}]
  /\ UNCHANGED <<\E>>

CreateChange(n, k, rep) ==
  /\ k \in PrivateKey
  /\ lastHash # NoHashVal
  /\ LET blk == [author |-> k, previous |-> lastHash,
                 kind |-> "change", data |-> rep]
         nh == CalculateHash(blk, lastHash)
     IN /\ lastHash' = nh
        /\ ledger' = [node \in Node |-> [ledger[node] EXCEPT ![nh] = blk]]
        /\ received' = [node \in Node |-> {nh}]
  /\ UNCHANGED <<\E>>

\* A node confirms a received block against its local ledger copy.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = ledger[n][h]]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesis(n, k)
  \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, rec \in PublicKey :
        CreateSend(n, k, amt, rec)
  \/ \E n \in Node, k \in PrivateKey, src \in PublicKey : CreateOpen(n, k, src)
  \/ \E n \in Node, k \in PrivateKey, src \in {NoHash} \cup Hash : CreateReceive(n, k, src)
  \/ \E n \in Node, k \in PrivateKey, rep \in PublicKey : CreateChange(n, k, rep)
  \/ \E n \in Node, h \in {NoHash} \cup Hash : Validate(n, h)

Spec == Init /\ [][Next]_Vars

\* Type invariant plus the cryptographic signature check.
SignatureValid ==
  /\ ledger \in Ledger
  /\ \A n \in Node : \A h \in {NoHash} \cup Hash :
       ledger[n][h] # NoBlockVal => ledger[n][h].author = h

SafetyInvariant == TypeOK /\ SignatureValid

====