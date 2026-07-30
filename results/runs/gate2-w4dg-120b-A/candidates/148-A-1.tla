---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Authors: ChatGPT (OpenAI)

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* BlockType is an enum naming the four payload types the Nano lattice
\* protocol supports: the genesis block, a balance-sending block, an account
\* opening block, and a change-representative block.
BlockType == {"GENESIS", "SEND", "OPEN", "CHANGE"}

\* A block records its type, the hash of the previous block in the sender's
\* chain, the hash of the source send block (if any), the amount it moves
\* (if any), and the public key of the block's owner.
Block ==
  [bt: BlockType,
   prevHash: Hash,
   source: Hash,
   amount: Nat,
   owner: PublicKey]

\* An empty ledger cell: NoBlock is the broadcast value machines put in the
\* ledger for every hash that has not been committed yet.
BlankLedger == [bt |-> "GENESIS", prevHash |-> NoHash, source |-> NoHash,
                amount |-> 0, owner |-> NoBlockVal]

RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHash
    THEN 0
    ELSE IF h = NoHashVal
      THEN 0
      ELSE LET b == Balance(Ledger[Node][h].prevHash) IN
           IF Ledger[Node][h].bt = "SEND" \/ Ledger[Node][h].bt = "CHANGE"
             THEN b
             ELSE
               IF Ledger[Node][h].bt = "OPEN"
                 THEN b + Ledger[Node][h].amount
                 ELSE b - Ledger[Node][h].amount

RECURSIVE TotalBalance(_)
TotalBalance(N) ==
  IF N = {}
    THEN 0
    ELSE LET n == CHOOSE x \in N : TRUE IN
         Balance(Ledger[n][NoHash]) + TotalBalance(N \ {n})

RECURSIVE TotalSupply(_)
TotalSupply(L) ==
  IF L = {}
    THEN 0
    ELSE LET h == CHOOSE x \in L : TRUE IN
         (IF Ledger[Node][h].bt = "GENESIS" THEN Ledger[Node][h].amount ELSE 0)
         + TotalSupply(L \ {h})

VARIABLES LastHash, Ledger, Received

vars == <<LastHash, Ledger, Received>>

TypeOK ==
  /\ LastHash \in Hash
  /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
  /\ Received \in [Node -> SUBSET Hash]

\* The cryptographic invariant ties the whole thing together: every committed
\* block must have a signature matching the owner chain it appears on.
SignatureValid ==
  \A n \in Node, h \in Hash :
    /\ Ledger[n][h] # NoBlock
    /\ LET sk == CHOOSE k \in PrivateKey : OwnerOf(k) = Ledger[n][h].owner
       IN Ed25519.Sign(sk, Ledger[n][h].owner) = Ledger[n][h].owner

Init ==
  /\ LastHash = NoHash
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ Received = [n \in Node |-> {}]

\* GENESIS: seeded once, written into every node's ledger together.
CreateGenesis(k) ==
  /\ LastHash = NoHash
  /\ LET h == CalculateHash("GENESIS", NoHash, NoHash, GenesisBalance) IN
     /\ LastHash' = h
     /\ Ledger' = [n \in Node |->
                     [Ledger[n] EXCEPT ![h] = [bt |-> "GENESIS",
                                                prevHash |-> NoHash,
                                                source |-> NoHash,
                                                amount |-> GenesisBalance,
                                                owner |-> OwnerOf(k)]]]
     /\ Received' = [n \in Node |->
                       [Received[n] EXCEPT ![h] = Received[n] \cup {h}]]

\* SEND: extends the sender's chain, debiting balance by the amount.
CreateSend(k, dest, amt) ==
  /\ LastHash # NoHash
  /\ LET h == CalculateHash("SEND", LastHash, NoHash, amt) IN
     /\ LastHash' = h
     /\ Ledger' = [n \in Node |->
                     [Ledger[n] EXCEPT ![h] = [bt |-> "SEND",
                                                prevHash |-> LastHash,
                                                source |-> NoHash,
                                                amount |-> amt,
                                                owner |-> OwnerOf(k)]]]
     /\ Received' = [n \in Node |->
                       [Received[n] EXCEPT ![h] = Received[n] \cup {h}]]

\* OPEN: the first block on a fresh account chain, seeded by a send.
CreateOpen(k, source) ==
  /\ Ledger' = [n \in Node |->
                 [Ledger[n] EXCEPT ![source] = [bt |-> "OPEN",
                                                prevHash |-> NoHash,
                                                source |-> source,
                                                amount |-> Ledger[n][source].amount,
                                                owner |-> OwnerOf(k)]]]
  /\ LastHash' = source
  /\ Received' = [n \in Node |->
                   [Received[n] EXCEPT ![source] = Received[n] \cup {source}]]

\* RECEIVE: a block that consumes a send block and credits the amount.
CreateReceive(k, source, recv) ==
  /\ LastHash # NoHash
  /\ Ledger' = [n \in Node |->
                 [Ledger[n] EXCEPT ![recv] = [bt |-> "RECEIVE",
                                               prevHash |-> LastHash,
                                               source |-> source,
                                               amount |-> Ledger[n][source].amount,
                                               owner |-> OwnerOf(k)]]]
  /\ LastHash' = recv
  /\ Received' = [n \in Node |->
                   [Received[n] EXCEPT ![recv] = Received[n] \cup {recv}]]

\* CHANGE: a no-op on balance that rotates the node's voting rep.
CreateChange(k) ==
  /\ LastHash # NoHash
  /\ LET h == CalculateHash("CHANGE", LastHash, NoHash, 0) IN
     /\ LastHash' = h
     /\ Ledger' = [n \in Node |->
                     [Ledger[n] EXCEPT ![h] = [bt |-> "CHANGE",
                                                prevHash |-> LastHash,
                                                source |-> NoHash,
                                                amount |-> 0,
                                                owner |-> OwnerOf(k)]]]
     /\ Received' = [n \in Node |->
                       [Received[n] EXCEPT ![h] = Received[n] \cup {h}]]

Validate(n, h) ==
  /\ h \in Received[n]
  /\ Ledger[n][h] = NoBlock
  /\ Ed25519.Verify(Ledger[n][h].owner,
                    Ed25519.Sign(CHOOSE k \in PrivateKey : OwnerOf(k) = Ledger[n][h].owner),
                    Ledger[n][h].owner)
  /\ Ledger' = [Ledger EXCEPT ![n][h] = Ledger[n][h]]
  /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
  /\ UNCHANGED LastHash

Next ==
  \/ \E k \in PrivateKey : CreateGenesis(k)
  \/ \E k \in PrivateKey, dest \in Node, amt \in Nat : CreateSend(k, dest, amt)
  \/ \E k \in PrivateKey, source \in Hash : CreateOpen(k, source)
  \/ \E k \in PrivateKey, source \in Hash, recv \in Hash : CreateReceive(k, source, recv)
  \/ \E k \in PrivateKey : CreateChange(k)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

\* The full spec: a safety-first spec with no progress claim.
Spec == Init /\ [][Next]_vars

\* TypeInvariant: a standard sanity check on the model's variables.
TypeInvariant == TypeOK

\* SafetyInvariant: the cryptographic claim the model's entire point is to
\* validate.
SafetyInvariant == SignatureValid

====