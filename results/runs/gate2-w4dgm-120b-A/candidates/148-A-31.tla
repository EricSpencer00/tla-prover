---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

\* The last calculated block hash (ordering in a block lattice).
\* The distributed ledger, replicated per node, mapping block hashes to signed blocks.
\* Blocks in transit to each node awaiting confirmation.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Blocks == [type: {"genesis", "send", "open", "receive", "change"},
           signer: PublicKey, prev: Hash \cup {NoHash}, target: PublicKey,
           amount: 0..GenesisBalance]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET (Hash \X Blocks)]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Compute the balance of an account by walking its block chain recursively.
BalanceOf(account, h) ==
  IF h = NoHash \/ ledger[account][h] = NoBlockVal
  THEN 0
  ELSE LET b == ledger[account][h] IN
       IF b.type = "send"
       THEN BalanceOf(account, b.prev) - b.amount
       ELSE IF b.type = "receive"
       THEN BalanceOf(account, b.prev) + b.amount
       ELSE BalanceOf(account, b.prev)

\* A block must be signed by the account's key, must extend an existing block in
\* the local copy, and must respect the account's balance or unclaimed-send status.
IsValidBlock(authNode, h, b) ==
  /\ ledger[authNode][h] = NoBlockVal
  /\ b.signer = PrivateKey[authNode]
  /\ IF lastHash = NoHashVal THEN h = NoHash ELSE h # NoHash
  /\ IF lastHash = NoHashVal THEN b.type = "genesis"
     ELSE IF b.type = "send" THEN
       /\ b.prev = lastHash
       /\ b.amount >= 1 /\ b.amount <= BalanceOf(authNode, lastHash)
       /\ b.target \in PublicKey
     ELSE IF b.type = "open" THEN
       /\ b.prev = NoHash
       /\ b.target = PublicKey[authNode]
       /\ \E src \in Node, sh \in Hash :
            /\ ledger[src][sh] # NoBlockVal
            /\ ledger[src][sh].type = "send"
            /\ ledger[src][sh].target = b.target
            /\ \A n2 \in Node : \A h2 \in Hash :
                 (ledger[n2][h2] # NoBlockVal /\ ledger[n2][h2].type = "receive")
                   => ledger[n2][h2].prev # sh
     ELSE IF b.type = "receive" THEN
       /\ b.prev # NoHash
       /\ \E src \in Node, sh \in Hash :
            /\ ledger[src][sh] # NoBlockVal
            /\ ledger[src][sh].type = "send"
            /\ ledger[src][sh].target = b.signer
            /\ ledger[src][sh].amount = b.amount
            /\ \A n2 \in Node : \A h2 \in Hash :
                 (ledger[n2][h2] # NoBlockVal /\ ledger[n2][h2].type = "receive")
                   => ledger[n2][h2].prev # sh
     ELSE IF b.type = "change" THEN
       /\ b.prev = lastHash
       /\ b.amount = 0
       /\ b.target = NoHash
       /\ TRUE
     ELSE FALSE

\* Genesis block: mint the entire supply and broadcast it to every node.
CreateGenesis(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([type |-> "genesis", signer |-> PublicKey[n], prev |-> NoHash,
                                target |-> NoHash, amount |-> GenesisBalance])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                        [type |-> "genesis", signer |-> PublicKey[n], prev |-> NoHash,
                         target |-> NoHash, amount |-> GenesisBalance]]]
  /\ received' = [m \in Node |-> {<<lastHash, [type |-> "genesis",
                         signer |-> PublicKey[n], prev |-> NoHash,
                         target |-> NoHash, amount |-> GenesisBalance]>>}
                    \cup received[m]]

CreateSend(n, amt) ==
  /\ lastHash # NoHashVal
  /\ amt >= 1 /\ amt <= BalanceOf(n, lastHash)
  /\ LET h == CalculateHash([type |-> "send", signer |-> PublicKey[n], prev |-> lastHash,
                             target |-> NoHash, amount |-> amt]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [type |-> "send", signer |-> PublicKey[n], prev |-> lastHash,
                           target |-> NoHash, amount |-> amt]]]
       /\ received' = [m \in Node |->
                         {<<h, [type |-> "send", signer |-> PublicKey[n], prev |-> lastHash,
                                 target |-> NoHash, amount |-> amt]>>}
                          \cup received[m]]

CreateOpen(n, sender, sh) ==
  /\ lastHash # NoHashVal
  /\ ledger[sender][sh] # NoBlockVal
  /\ ledger[sender][sh].type = "send"
  /\ ledger[sender][sh].target = PublicKey[n]
  /\ \A n2 \in Node : \A h2 \in Hash :
       (ledger[n2][h2] # NoBlockVal /\ ledger[n2][h2].type = "receive")
         => ledger[n2][h2].prev # sh
  /\ LET h == CalculateHash([type |-> "open", signer |-> PublicKey[n], prev |-> NoHash,
                             target |-> NoHash, amount |-> ledger[sender][sh].amount]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [type |-> "open", signer |-> PublicKey[n], prev |-> NoHash,
                           target |-> NoHash, amount |-> ledger[sender][sh].amount]]]
       /\ received' = [m \in Node |->
                         {<<h, [type |-> "open", signer |-> PublicKey[n], prev |-> NoHash,
                                 target |-> NoHash,
                                 amount |-> ledger[sender][sh].amount]>>}
                          \cup received[m]]

CreateReceive(n, sender, sh) ==
  /\ lastHash # NoHashVal
  /\ ledger[sender][sh] # NoBlockVal
  /\ ledger[sender][sh].type = "send"
  /\ ledger[sender][sh].target = PublicKey[n]
  /\ \A n2 \in Node : \A h2 \in Hash :
       (ledger[n2][h2] # NoBlockVal /\ ledger[n2][h2].type = "receive")
         => ledger[n2][h2].prev # sh
  /\ LET h == CalculateHash([type |-> "receive", signer |-> PublicKey[n], prev |-> lastHash,
                             target |-> sender, amount |-> ledger[sender][sh].amount]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [type |-> "receive", signer |-> PublicKey[n], prev |-> lastHash,
                           target |-> sender, amount |-> ledger[sender][sh].amount]]]
       /\ received' = [m \in Node |->
                         {<<h, [type |-> "receive", signer |-> PublicKey[n], prev |-> lastHash,
                                 target |-> sender,
                                 amount |-> ledger[sender][sh].amount]>>}
                          \cup received[m]]

CreateChange(n) ==
  /\ lastHash # NoHashVal
  /\ LET h == CalculateHash([type |-> "change", signer |-> PublicKey[n], prev |-> lastHash,
                             target |-> NoHash, amount |-> 0]) IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [type |-> "change", signer |-> PublicKey[n], prev |-> lastHash,
                           target |-> NoHash, amount |-> 0]]]
       /\ received' = [m \in Node |->
                         {<<h, [type |-> "change", signer |-> PublicKey[n], prev |-> lastHash,
                                 target |-> NoHash, amount |-> 0]>>}
                          \cup received[m]]

\* A node validates a received block against its own copy before accepting it.
ProcessBlock(n, h, b) ==
  /\ <<h, b>> \in received[n]
  /\ IsValidBlock(n, h, b)
  /\ ledger' = [ledger EXCEPT ![n][h] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {<<h, b>>}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesis(n) \/ CreateChange(n)
  \/ \E n \in Node, amt \in 1..GenesisBalance : CreateSend(n, amt)
  \/ \E n \in Node, sender \in Node, sh \in Hash : CreateOpen(n, sender, sh)
  \/ \E n \in Node, sender \in Node, sh \in Hash : CreateReceive(n, sender, sh)
  \/ \E n \in Node, h \in Hash, b \in Blocks : ProcessBlock(n, h, b)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A n \in Node : WF_vars(\E h \in Hash, b \in Blocks : ProcessBlock(n, h, b)))

\* Every block in every node's ledger has a valid signature matching its account.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    (ledger[n][h] # NoBlockVal) => ledger[n][h].signer = PublicKey[n]

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET (Hash \X Blocks)]

====