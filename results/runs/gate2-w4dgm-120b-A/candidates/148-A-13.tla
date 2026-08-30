---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(* The original Nano blockchain's block-lattice protocol, modeled for a bounded set  *)
(* of block hashes, with a focus on hash functions and signature checking.           *)

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

(* The hash calculation is abstracted as a constant operator; a concrete version     *)
(* (usually a bounded or finite approximation) is substituted in the .cfg file.     *)
CONSTANTS CalculateHash, NoHash, NoBlock

NONE == "none"

VARIABLES lastHash, ledger, received, nodeKey

vars == <<lastHash, ledger, received, nodeKey>>

PublicKeyOf(k) == CHOOSE p \in PublicKey : p = k

AccountBalance(node) == RECURSIVE AccountBalance(_)
AccountBalance(n) ==
  IF n <= 0 THEN 0
  ELSE
    LET blk == ledger[n][CalcHash(n, n - 1)]
    IN IF blk = NoBlockVal THEN 0
       ELSE blk.amount + AccountBalance(n - 1)

TotalBalance == AccountBalance(Node)

TypeOK ==
  /\ lastHash \in {NoHash} \cup Hash
  /\ ledger \in [1..Node -> [Hash -> {NoBlockVal} \cup [sender: PrivateKey, amount: 1..GenesisBalance, hash: Hash]]]
  /\ received \in [Node -> SUBSET [sender: PrivateKey, amount: 1..GenesisBalance, hash: Hash]]
  /\ nodeKey \in [Node -> PrivateKey]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in 1..Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]
  /\ nodeKey = [n \in Node |-> CHOOSE k \in PrivateKey : TRUE]

CalcHash(i, h) == CalculateHash([sender |-> nodeKey[i], amount |-> 1], h)

CreateGenesis ==
  /\ lastHash = NoHash
  /\ lastHash' = CalcHash(1, NoHash)
  /\ ledger' = [n \in 1..Node |-> [ledger[n] EXCEPT ![CalcHash(1, NoHash)] = [sender |-> nodeKey[1], amount |-> GenesisBalance, hash |-> CalcHash(1, NoHash)]]]
  /\ received' = [n \in Node |-> {}]
  /\ UNCHANGED nodeKey

CreateSendBlock(i) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalcHash(i, lastHash)
  /\ ledger' = [n \in 1..Node |-> [ledger[n] EXCEPT ![CalcHash(i, lastHash)] = [sender |-> nodeKey[i], amount |-> 1, hash |-> CalcHash(i, lastHash)]]]
  /\ received' = [n \in Node |-> received[n] \cup {[sender |-> nodeKey[i], amount |-> 1, hash |-> CalcHash(i, lastHash)]}]
  /\ UNCHANGED nodeKey

ValidateBlock(i, blk) ==
  /\ blk \in received[i]
  /\ ledger[i][blk.hash] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![i][blk.hash] = blk]
  /\ received' = [received EXCEPT ![i] = received[i] \ {blk}]
  /\ UNCHANGED <<lastHash, nodeKey>>

ValidateAny(i) ==
  /\ \E blk \in received[i] : ledger[i][blk.hash] = NoBlockVal /\ ledger' = [ledger EXCEPT ![i][blk.hash] = blk] /\ received' = [received EXCEPT ![i] = received[i] \ {blk}]
  /\ UNCHANGED <<lastHash, nodeKey>>

Next ==
  \/ CreateGenesis
  \/ \E i \in Node : CreateSendBlock(i)
  \/ \E i \in Node, blk \in received[i] : ValidateBlock(i, blk)
  \/ \E i \in Node : ValidateAny(i)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  /\ TypeOK
  /\ \A n \in 1..Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sender = PublicKeyOf(PublicKey)

====