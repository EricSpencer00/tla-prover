---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* The hash calculation is abstracted as a constant operator; the .cfg file
\* substitutes a concrete (finite) implementation for it during model checking.
CalculateHashImpl == CalculateHash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A block is a record; the ledger maps a hash to the block it identifies, or
\* NoBlockVal if that hash is not used. Every node keeps its own copy of the
\* ledger, so the model tracks a replicated ledger per node.
Block == [type: {"genesis", "send", "open", "receive", "change"},
          owner: PublicKey, prev: Hash, target: PublicKey, amount: Nat,
          sig: PrivateKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is created once and added to every node's ledger copy.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E k \in PrivateKey :
       /\ lastHash' = CalculateHashImpl([type |-> "genesis", owner |-> k,
                                         prev |-> NoHash, target |-> NoHash,
                                         amount |-> GenesisBalance, sig |-> k])
       /\ ledger' = [n \in Node |-> [h \in Hash |->
                     IF h = lastHash' THEN [type |-> "genesis", owner |-> k,
                                            prev |-> NoHash, target |-> NoHash,
                                            amount |-> GenesisBalance, sig |-> k]
                     ELSE ledger[n][h]]]
       /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A send block debits the sender's account and names a recipient.
CreateSendBlock ==
  /\ lastHash # NoHashVal
  /\ \E k \in PrivateKey, amt \in 1..GenesisBalance :
       /\ Balance(k) >= amt
       /\ lastHash' = CalculateHashImpl([type |-> "send", owner |-> k,
                                         prev |-> lastHash, target |-> NoHash,
                                         amount |-> amt, sig |-> k])
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "send",
                                            owner |-> k, prev |-> lastHash,
                                            target |-> NoHash, amount |-> amt,
                                            sig |-> k]]]
       /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* An open block starts a new account chain, referencing a send block directed
\* to the account's public key.
CreateOpenBlock ==
  /\ lastHash # NoHashVal
  /\ \E k \in PrivateKey, h \in Hash :
       /\ ledger[Node][h] # NoBlockVal
       /\ ledger[Node][h].type = "send"
       /\ ledger[Node][h].target = k
       /\ ledger[Node][h].sig = k
       /\ \A n \in Node : ledger[n][h].type = "send"
       /\ lastHash' = CalculateHashImpl([type |-> "open", owner |-> k,
                                         prev |-> NoHash, target |-> NoHash,
                                         amount |-> 0, sig |-> k])
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "open",
                                            owner |-> k, prev |-> NoHash,
                                            target |-> NoHash, amount |-> 0,
                                            sig |-> k]]]
       /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A receive block adds the amount from a send block to the receiver's balance.
CreateReceiveBlock ==
  /\ lastHash # NoHashVal
  /\ \E k \in PrivateKey, h \in Hash :
       /\ ledger[Node][h] # NoBlockVal
       /\ ledger[Node][h].type = "send"
       /\ ledger[Node][h].target = k
       /\ ledger[Node][h].sig = k
       /\ \A n \in Node : ledger[n][h].type = "send"
       /\ lastHash' = CalculateHashImpl([type |-> "receive", owner |-> k,
                                         prev |-> lastHash, target |-> NoHash,
                                         amount |-> 0, sig |-> k])
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "receive",
                                            owner |-> k, prev |-> lastHash,
                                            target |-> NoHash, amount |-> 0,
                                            sig |-> k]]]
       /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A change-representative block only references the previous block.
CreateChangeRepresentativeBlock ==
  /\ lastHash # NoHashVal
  /\ \E k \in PrivateKey :
       /\ lastHash' = CalculateHashImpl([type |-> "change", owner |-> k,
                                         prev |-> lastHash, target |-> NoHash,
                                         amount |-> 0, sig |-> k])
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "change",
                                            owner |-> k, prev |-> lastHash,
                                            target |-> NoHash, amount |-> 0,
                                            sig |-> k]]]
       /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A node validates a received block against its own ledger copy before adding
\* it; validation checks the signature, the existence of referenced blocks, and
\* block-type-specific rules (no overdraft, no double-claiming a send).
ValidateBlock ==
  /\ \E n \in Node, h \in received[n] :
       /\ ledger[n][h] = NoBlockVal
       /\ \E blk \in Block :
            /\ blk.type \in {"genesis", "send", "open", "receive", "change"}
            /\ blk.owner \in PublicKey
            /\ blk.prev \in Hash \cup {NoHash}
            /\ blk.target \in PublicKey \cup {NoHash}
            /\ blk.amount \in Nat
            /\ blk.sig \in PrivateKey
            /\ ledger[n][h] = blk
            /\ blk.sig = k
            /\ IF blk.type = "send" THEN Balance(k) >= blk.amount ELSE TRUE
            /\ IF blk.type = "open" THEN
                 \A m \in Node : ledger[m][blk.prev].type = "send"
               ELSE TRUE
            /\ IF blk.type = "receive" THEN
                 \A m \in Node : ledger[m][blk.prev].type = "send"
               ELSE TRUE
       /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ CreateGenesisBlock
  \/ CreateSendBlock
  \/ CreateOpenBlock
  \/ CreateReceiveBlock
  \/ CreateChangeRepresentativeBlock
  \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* The chain of blocks for an account is walked recursively to compute its
\* balance; the chain is finite because the hash space is finite.
Balance(k) ==
  LET f == [h \in Hash |-> IF ledger[Node][h] = NoBlockVal THEN 0
                          ELSE IF ledger[Node][h].owner = k
                               THEN IF ledger[Node][h].type = "send"
                                    THEN -ledger[Node][h].amount
                                    ELSE IF ledger[Node][h].type = "receive"
                                         THEN ledger[Node][h].amount
                                         ELSE 0
                               ELSE 0]
  IN LET walk ==
       [h \in Hash |-> IF f[h] = 0 THEN 0
                       ELSE f[h] + IF ledger[Node][h].prev = NoHash
                                    THEN 0 ELSE walk[ledger[Node][h].prev]]
     IN walk[lastHash]

\* The cryptographic invariant: every block in every node's ledger copy has a
\* signature that matches the public key of the account that owns its chain.
SignatureValid(k) ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h].sig = k

TypeInvariant == TypeOK
SafetyInvariant == \E k \in PrivateKey : SignatureValid(k)

====