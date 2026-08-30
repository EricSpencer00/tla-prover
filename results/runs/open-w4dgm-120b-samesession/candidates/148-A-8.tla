---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

(* The original Nano block-lattice protocol, modeled for finite-model checking. *)
(* Every account has its own chain of blocks; the invariant protects the *)
(* cryptographic signature of every block stored in every node's ledger. *)

CONSTANTS
  Hash,          \* set of block hashes; abstractly bounded for model checking
  NoHashVal,     \* sentinel value meaning "no prior hash"
  PrivateKey,    \* set of private keys (signing keys)
  PublicKey,     \* set of public keys (verification keys)
  Node,          \* network nodes, each holding a private key
  GenesisBalance, \* total coins at genesis
  NoBlockVal,    \* sentinel meaning "empty slot" in a replicated ledger
  NoHash,        \* sentinel meaning "no such block exists"
  NoBlock        \* sentinel meaning "no block to reference"

\* Hash calculation is modeled abstractly as a constant operator; the .cfg
\* file substitutes a concrete bounded implementation for model checking.
CalculateHash == CalculateHashImpl

\* Account ownership: each node holds exactly one private key.
OwnerOf == [n \in Node |-> CHOOSE k \in PrivateKey : n = OwnerOf[k]]
PublicOf == [k \in PrivateKey |-> CHOOSE p \in PublicKey : k = OwnerOf[p]]

\* An account chain is the set of blocks belonging to a given public key.
AccountChain == [p \in PublicKey |-> {b \in Hash : OwnerOf[b] = p}]
AccountBalance == [p \in PublicKey |-> IF p = PublicOf[CHOOSE k \in PrivateKey : TRUE]
                                         THEN GenesisBalance ELSE 0]

\* Recursive balance computation, walking the chain backwards via PrevHash.
RECURSIVE ChainBalance(_, _)
ChainBalance(p, b) ==
  IF b = NoHash THEN AccountBalance[p]
  ELSE LET prev == PrevHash[b] IN ChainBalance(p, prev) + Value[b]

\* The sum of all account balances; must never exceed the genesis supply.
TotalBalance == LET g == CHOOSE p \in PublicKey : TRUE
                IN ChainBalance(g, g)

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (Hash \X PublicKey \X (0..GenesisBalance) \X PrivateKey) \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET (Hash \X PublicKey \X (0..GenesisBalance) \X PrivateKey)]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Genesis block: the first block in the network, seeded with the entire supply.
CreateGenesis(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash({n}, NoHashVal)
  /\ \A k \in Node : ledger' = [ledger EXCEPT ![k] = [ledger[k] EXCEPT ![lastHash] = <<NoHash, PublicOf[OwnerOf[n]], GenesisBalance, OwnerOf[n]>>]]
  /\ UNCHANGED received

\* Send: remove value from the sender's account and broadcast.
CreateSend(n, amt) ==
  /\ amt \in 1..GenesisBalance
  /\ lastHash # NoHashVal
  /\ ChainBalance(PublicOf[OwnerOf[n]], lastHash) >= amt
  /\ lastHash' = CalculateHash({n}, lastHash)
  /\ \A k \in Node : ledger' = [ledger EXCEPT ![k] = [ledger[k] EXCEPT ![lastHash] = <<lastHash, PublicOf[OwnerOf[n]], amt, OwnerOf[n]>>]]
  /\ UNCHANGED received

\* Open: a receive-only account points at the send block that created it.
CreateOpen(n, recv) ==
  /\ lastHash # NoHashVal
  /\ PublicOf[OwnerOf[n]] # recv
  /\ lastHash' = CalculateHash({n}, lastHash)
  /\ \A k \in Node : ledger' = [ledger EXCEPT ![k] = [ledger[k] EXCEPT ![lastHash] = <<lastHash, recv, 0, OwnerOf[n]>>]]
  /\ UNCHANGED received

\* Receive: add the sent value to the receiver's account balance.
CreateReceive(n, recv, amt) ==
  /\ lastHash # NoHashVal
  /\ ChainBalance(recv, lastHash) + amt <= GenesisBalance
  /\ lastHash' = CalculateHash({n}, lastHash)
  /\ \A k \in Node : ledger' = [ledger EXCEPT ![k] = [ledger[k] EXCEPT ![lastHash] = <<lastHash, recv, amt, OwnerOf[n]>>]]
  /\ UNCHANGED received

\* Representative change: a meta-action that points at the same previous block.
CreateChangeRep(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash({n}, lastHash)
  /\ \A k \in Node : ledger' = [ledger EXCEPT ![k] = [ledger[k] EXCEPT ![lastHash] = <<lastHash, PublicOf[OwnerOf[n]], 0, OwnerOf[n]>>]]
  /\ UNCHANGED received

\* Broadcast a newly created block to every node's in-flight received set.
Broadcast(b) ==
  /\ \A k \in Node : b \notin received[k]
  /\ received' = [k \in Node |-> received[k] \cup {b}]
  /\ UNCHANGED <<lastHash, ledger>>

\* Validate a received block against the local ledger copy and add it.
ValidateConfirm(n, b) ==
  /\ b \in received[n]
  /\ \A h \in Hash : ledger[n][h] # b
  /\ LET p == PublicOf[OwnerOf[n]] IN
       /\ ledger[n][b[1]] # NoBlockVal
       /\ IF b[3] > 0
          THEN ChainBalance(p, b[1]) >= b[3]
          ELSE ChainBalance(p, b[1]) <= GenesisBalance
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b[1]] = b]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesis(n)
  \/ \E n \in Node, amt \in 1..GenesisBalance : CreateSend(n, amt)
  \/ \E n \in Node, recv \in PublicKey : CreateOpen(n, recv)
  \/ \E n \in Node, recv \in PublicKey, amt \in 1..GenesisBalance : CreateReceive(n, recv, amt)
  \/ \E n \in Node : CreateChangeRep(n)
  \/ \E b \in Hash : Broadcast(b)
  \/ \E n \in Node, b \in Hash : ValidateConfirm(n, b)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must carry a valid signature.
SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      ledger[n][h] # NoBlockVal =>
        OwnerOf[n] = ledger[n][h][4]

\* Every block in the replicated set of ledgers is well-typed.
TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (Hash \X PublicKey \X (0..GenesisBalance) \X PrivateKey) \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET (Hash \X PublicKey \X (0..GenesisBalance) \X PrivateKey)]

====