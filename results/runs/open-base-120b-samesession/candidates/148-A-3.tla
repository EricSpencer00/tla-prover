---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Hash,               \* Set of possible block hashes
    NoHashVal,          \* Sentinel value representing “no hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value representing “no block”
    CalculateHash,      \* Abstract hash function (will be overridden)
    NoHash,             \* Alias for NoHashVal used in the spec
    NoBlock,            \* Alias for NoBlockVal used in the spec
    PrivateToPublic,    \* Mapping from private keys to public keys
    NodeKey             \* Mapping from each node to its private key

(*--------------------------------------------------------------------
  Basic definitions
--------------------------------------------------------------------*)
\* Block types
BlockTypes == {"Genesis", "Send", "Open", "Receive", "Change"}

\* Block record definition (the hash of the block is stored explicitly)
Block ==
    [ type     : BlockTypes,
      prev     : Hash \/ {NoHash},
      account  : PublicKey,
      amount   : Nat,
      balance  : Nat,
      sig      : [ key : PrivateKey, hash : Hash ],
      hash     : Hash ]

\* Sentinel values (aliases for readability)
NoHash == NoHashVal
NoBlock == NoBlockVal

\* The set of all possible block values (including the sentinel)
BlockSet == Block \/ {NoBlock}

\* Validity of a block's signature
ValidSignature(b) ==
    /\ b \in Block
    /\ PrivateToPublic[b.sig.key] = b.account
    /\ b.sig.hash = b.hash

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    LastHash,   \* The most recent block hash (or NoHash)
    Ledger,     \* Ledger[n][h] = the block with hash h stored at node n
    Received    \* Received[n] = set of hashes pending validation at node n

(*--------------------------------------------------------------------
  Type invariant (declared as a separate operator)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ LastHash \in Hash \/ LastHash = NoHash
    /\ Ledger \in [Node -> [Hash -> BlockSet]]
    /\ Received \in [Node -> SUBSET Hash]

(*--------------------------------------------------------------------
  Safety invariant: every stored block has a valid signature
--------------------------------------------------------------------*)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF Ledger[n][h] # NoBlock
            THEN ValidSignature(Ledger[n][h])
            ELSE TRUE

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]

(*--------------------------------------------------------------------
  Helper: create a new block (generic)
--------------------------------------------------------------------*)
CreateBlock(b) ==
    /\ b \in Block
    /\ b.prev = LastHash
    /\ b.hash = CalculateHash(b, LastHash)
    /\ LastHash' = b.hash
    /\ Ledger' = [n \in Node |-> Ledger[n] @@ [b.hash |-> b]]
    /\ Received' = [n \in Node |-> Received[n] \cup {b.hash}]
    /\ UNCHANGED <<>>

(*--------------------------------------------------------------------
  Specific block‑creation actions
--------------------------------------------------------------------*)

\* 1. Genesis block – can happen only once
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E n \in Node :
         LET pk == NodeKey[n] IN
         LET pkPub == PrivateToPublic[pk] IN
         LET b ==
            [ type     |-> "Genesis",
              prev     |-> NoHash,
              account  |-> pkPub,
              amount   |-> GenesisBalance,
              balance  |-> GenesisBalance,
              sig      |-> [key |-> pk, hash |-> NoHash],
              hash     |-> NoHash ] \* temporary hash, will be recomputed
         IN
         CreateBlock(b)

\* 2. Send block – reduces sender’s balance
CreateSend(sender, recipientPub, amt) ==
    /\ sender \in Node
    /\ recipientPub \in PublicKey
    /\ amt \in Nat
    /\ \E pk == NodeKey[sender] :
        LET senderPub == PrivateToPublic[pk] IN
        \E prevBlock \in Block :
            /\ Ledger[sender][prevBlock.hash] = prevBlock
            /\ prevBlock.account = senderPub
            /\ prevBlock.balance >= amt
            /\ LET newBal == prevBlock.balance - amt IN
               LET b ==
                 [ type     |-> "Send",
                   prev     |-> LastHash,
                   account  |-> senderPub,
                   amount   |-> amt,
                   balance  |-> newBal,
                   sig      |-> [key |-> pk, hash |-> LastHash],
                   hash     |-> NoHash ] \* hash filled by CreateBlock
               IN
               CreateBlock(b)

\* 3. Open block – creates a new account from a received send
CreateOpen(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ \E pk == NodeKey[node] :
        LET nodePub == PrivateToPublic[pk] IN
        \E sendBlock \in Block :
            /\ Ledger[node][sendHash] = sendBlock
            /\ sendBlock.type = "Send"
            /\ sendBlock.account # nodePub
            /\ sendBlock.amount \in Nat
            /\ LET b ==
                 [ type     |-> "Open",
                   prev     |-> LastHash,
                   account  |-> nodePub,
                   amount   |-> sendBlock.amount,
                   balance  |-> sendBlock.amount,
                   sig      |-> [key |-> pk, hash |-> LastHash],
                   hash     |-> NoHash ]
               IN
               CreateBlock(b)

\* 4. Receive block – claims a pending send
CreateReceive(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ \E pk == NodeKey[node] :
        LET nodePub == PrivateToPublic[pk] IN
        \E sendBlock \in Block :
            /\ Ledger[node][sendHash] = sendBlock
            /\ sendBlock.type = "Send"
            /\ sendBlock.account # nodePub
            /\ \E prevBlock \in Block :
                /\ Ledger[node][prevBlock.hash] = prevBlock
                /\ prevBlock.account = nodePub
                /\ prevBlock.type # "Open" \/ prevBlock.type # "Receive" \/ prevBlock.type # "Send"
                /\ LET newBal == prevBlock.balance + sendBlock.amount IN
                   LET b ==
                     [ type     |-> "Receive",
                       prev     |-> LastHash,
                       account  |-> nodePub,
                       amount   |-> sendBlock.amount,
                       balance  |-> newBal,
                       sig      |-> [key |-> pk, hash |-> LastHash],
                       hash     |-> NoHash ]
                   IN
                   CreateBlock(b)

\* 5. Change representative block
CreateChange(node, newRep) ==
    /\ node \in Node
    /\ newRep \in PublicKey
    /\ \E pk == NodeKey[node] :
        LET nodePub == PrivateToPublic[pk] IN
        \E prevBlock \in Block :
            /\ Ledger[node][prevBlock.hash] = prevBlock
            /\ prevBlock.account = nodePub
            /\ LET b ==
                 [ type     |-> "Change",
                   prev     |-> LastHash,
                   account  |-> nodePub,
                   amount   |-> 0,
                   balance  |-> prevBlock.balance,
                   sig      |-> [key |-> pk, hash |-> LastHash],
                   hash     |-> NoHash ]
               IN
               CreateBlock(b)

\* 6. Process a received block at a node (validation)
ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in Received[node] :
        LET b == Ledger[node][h] IN
        /\ b # NoBlock
        /\ ValidSignature(b)
        /\ Received' = [n \in Node |-> IF n = node THEN Received[n] \ {h} ELSE Received[n]]
        /\ UNCHANGED <<LastHash, Ledger>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ CreateGenesis
    \/ \E s \in Node, r \in PublicKey, a \in Nat : CreateSend(s, r, a)
    \/ \E n \in Node, sh \in Hash : CreateOpen(n, sh)
    \/ \E n \in Node, sh \in Hash : CreateReceive(n, sh)
    \/ \E n \in Node, rp \in PublicKey : CreateChange(n, rp)
    \/ \E n \in Node : ProcessReceived(n)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

(*--------------------------------------------------------------------
  Operators required by the configuration file
--------------------------------------------------------------------*)
\* The concrete implementation of the hash function (overridden in the .cfg)
CalculateHashImpl(data, prev) ==
    IF data = NoBlockVal THEN NoHashVal
    ELSE CHOOSE h \in Hash: TRUE

====