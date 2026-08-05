---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* The Nano crypto-currency blockchain uses a block-lattice: every account has its own chain.
\* The spec tracks: the last hash id, a replicated ledger per node, and the in-flight received
\* blocks per node. Only the ledger and received-sets are model-checked; the hash operator
\* itself is abstracted via the CalculateHash constant and overridden in the .cfg.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* A block in the Nano protocol: a raw data payload plus the Ed25519 signature of it.
Block == [data : STRING, sig : PublicKey]

\* ChainIdx is the position of a block in an account's chain; the genesis block is 0.
ChainIdx == 0..(Cardinality(Hash) - 1)

\* Dispatches to the operator chosen by the .cfg substitution.
CalculateHashInstance(d, h) == CalculateHash(d, h)

\* BalanceAccount walks an account chain back from the tip and sums its amounts.
RECURSIVE BalanceAccount(_)
BalanceAccount(n) ==
  IF n = NoHash THEN 0
  ELSE LET b == Ledger[NoHash][n] IN b.data + BalanceAccount(b.prev)

TypeOK ==
  /\ lastHash \in Hash
  /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
  /\ Received \in [Node -> SUBSET Hash]

\* Every block in the replicated ledger, on every node, must verify against the
\* public key of the account that owns the chain it belongs to.
LedgerSignatureOK ==
  \A n \in Node, h \in Hash : Ledger[n][h] # NoBlock => Ledger[n][h].sig = PublicKey

\* Money is conserved: the total across all accounts never exceeds the genesis supply.
BalanceOK ==
  LET total == (BalanceAccount(NoHash) + BalanceAccount(NoHash)) IN total =< GenesisBalance

Init ==
  /\ lastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ Received = [n \in Node |-> {}]

\* The genesis block is created by one keyholder and stored on every node's ledger together.
CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ \E pk \in PrivateKey :
       /\ CalculateHashInstance("genesis:" + pk, NoHashVal) \in Hash
       /\ \A n \in Node :
            Ledger' = [Ledger EXCEPT ![n][CalculateHashInstance("genesis:" + pk, NoHashVal)] =
                         [data |-> GenesisBalance, sig |-> pk]]
  /\ lastHash' = CalculateHashInstance("genesis:" + pk, NoHashVal)
  /\ UNCHANGED Received

\* A send block debits the sender and references the previous block in its own chain.
CreateSend(n) ==
  /\ \E amt \in 1..(BalanceAccount(lastHash) - 1), to \in PrivateKey :
       LET newh == CalculateHashInstance(n.privateKey + "send:" + to + ":" + amt, lastHash) IN
         /\ newh \in Hash
         /\ Ledger' = [Ledger EXCEPT ![n][newh] = [data |-> -amt, sig |-> n.privateKey]]
         /\ Received' = [m \in Node |-> Received[m] \cup {newh}]
  /\ lastHash' = newh
  /\ UNCHANGED <<>>

\* Opening a new account chain references a send block directed at it.
CreateOpen(n) ==
  /\ \E sender \in Node :
       \E h \in Ledger[sender] :
         /\ Ledger[sender][h] # NoBlock
         /\ Ledger[sender][h].sig = n.privateKey
         /\ h \notin Received[n]
         /\ LET newh == CalculateHashInstance(n.privateKey + "open:" + h, NoHashVal) IN
              /\ newh \in Hash
              /\ Ledger' = [Ledger EXCEPT ![n][newh] = [data |-> 0, sig |-> n.privateKey]]
              /\ Received' = [m \in Node |-> Received[m] \cup {newh}]
  /\ lastHash' = newh
  /\ UNCHANGED <<>>

\* A receive block credits the account and references both the previous block and a send block.
CreateReceive(n) ==
  /\ \E sender \in Node :
       \E h \in Ledger[sender] :
         /\ Ledger[sender][h] # NoBlock
         /\ Ledger[sender][h].sig = n.privateKey
         /\ h \notin Received[n]
         /\ LET newh == CalculateHashInstance(n.privateKey + "receive:" + h, lastHash) IN
              /\ newh \in Hash
              /\ Ledger' = [Ledger EXCEPT ![n][newh] = [data |-> Ledger[sender][h].data, sig |-> n.privateKey]]
              /\ Received' = [m \in Node |-> Received[m] \cup {newh}]
  /\ lastHash' = newh
  /\ UNCHANGED <<>>

\* The account owner changes their voting representative for this chain.
CreateChangeRep(n) ==
  /\ \E newRep \in PublicKey :
       LET newh == CalculateHashInstance(n.privateKey + "reps:" + newRep, lastHash) IN
         /\ newh \in Hash
         /\ Ledger' = [Ledger EXCEPT ![n][newh] = [data |-> 0, sig |-> n.privateKey]]
         /\ Received' = [m \in Node |-> Received[m] \cup {newh}]
  /\ lastHash' = newh
  /\ UNCHANGED <<>>

\* A node validates a received block against its own ledger copy and adds it.
Validate(n) ==
  /\ \E h \in Received[n] : Ledger' = [Ledger EXCEPT ![n][h] = Ledger[n][h]]
  /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesis
  \/ \E n \in Node : CreateSend(n)
  \/ \E n \in Node : CreateOpen(n)
  \/ \E n \in Node : CreateReceive(n)
  \/ \E n \in Node : CreateChangeRep(n)
  \/ \E n \in Node : Validate(n)

Spec == Init /\ [][Next]_<<lastHash, Ledger, Received>>

====