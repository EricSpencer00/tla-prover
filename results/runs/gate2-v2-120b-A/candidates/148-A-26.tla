---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Hash,           \* Universe of possible hashes (finite for model checking)
    NoHashVal,      \* Sentinel value meaning "no hash yet"
    PrivateKey,     
    PublicKey,      
    Node,           
    GenesisBalance, \* Total supply (natural number)
    NoBlockVal,     \* Sentinel for empty block slots
    CalculateHash,  \* Abstract hash function: calculates a new hash from block data + previous hash
    NoHash,         \* Alias for NoHashVal (kept for compatibility with cfg)
    NoBlock         \* Alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
HashSet == Hash
NodeSet == Node
KeySet  == PrivateKey
PubKeySet == PublicKey

\* ----------------------------------------------------------------------
\* Account identifiers are public keys
\* ----------------------------------------------------------------------
Account == PublicKey

\* ----------------------------------------------------------------------
\* Block structure (record)
\* ----------------------------------------------------------------------
BLOCK_FIELDS == {"type", "prev", "dest", "repr", "amount", "sig", "pub"}

\* Type of a block; fields not used by a particular type are set to NoBlock/NoHash
Block == [type : {"Genesis", "Send", "Open", "Receive", "Change"},
          prev : HashSet \cup {NoHash},
          dest : Account \cup {NoBlock},
          repr : Account \cup {NoBlock},
          amount : Nat \cup {NoBlock},
          sig   : PubKeySet,
          pub   : PubKeySet]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,          \* Hash of the most recent block created in the system
    ledger,            \* [node -> [hash -> Block or NoBlock]]
    received           \* [node -> SUBSET Hash] blocks pending validation

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
InitLedger == [n \in Node |-> [h \in Hash |-> NoBlock]]
InitReceived == [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Genesis block construction (deterministic fields)
\* ----------------------------------------------------------------------
GenesisBlock == [type   |-> "Genesis",
                 prev   |-> NoHash,
                 dest   |-> NoBlock,
                 repr   |-> NoBlock,
                 amount |-> GenesisBalance,
                 sig    |-> NoBlock,   \* No signature needed for genesis
                 pub    |-> NoBlock]   \* No owner (sentinel)

\* ----------------------------------------------------------------------
\* Balance computation for an account on a given node
\* Walk the account chain backwards from the latest block belonging to that account.
\* ----------------------------------------------------------------------
AccountChain(n, a) ==
    { h \in Hash : 
        LET b == ledger[n][h] IN
        b.type /= "Genesis" /\ b.pub = a }

\* Determine the latest block hash for account a on node n (or NoHash)
LatestHash(n, a) ==
    IF \E h \in AccountChain(n, a) : TRUE THEN
        CHOOSE h \in AccountChain(n, a) : 
            \A h2 \in AccountChain(n, a) : 
                \A t \in Nat : 
                    (CalculateHash(t, h2) # h)   \* abstract ordering placeholder
    ELSE NoHash

\* Compute balance of account a on node n
Balance(n, a) ==
    IF a = NoBlock THEN 0
    ELSE
        LET bh == LatestHash(n, a) IN
        IF bh = NoHash THEN 0
        ELSE
            LET b == ledger[n][bh] IN
            CASE b.type = "Genesis" -> b.amount
                 [] b.type = "Open"   -> b.amount
                 [] b.type = "Send"   -> -b.amount
                 [] b.type = "Receive"-> b.amount
                 [] b.type = "Change" -> 0
                 [] OTHER            -> 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger  = InitLedger
    /\ received = InitReceived

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash          \* Only allowed when no other block exists
    /\ ledger' = [n \in Node |-> 
                    [h \in Hash |-> 
                        IF h = CalculateHash("Genesis", NoHash) THEN GenesisBlock ELSE NoBlock]]
    /\ lastHash' = CalculateHash("Genesis", NoHash)
    /\ received' = InitReceived

CreateSend(n, to, amt) ==
    /\ n \in Node
    /\ to \in Account
    /\ amt \in Nat
    /\ amt <= Balance(n, ledger[n][lastHash].pub)   \* cannot overdraft
    /\ \E prevHash \in Hash :
          ledger[n][prevHash].pub = ledger[n][lastHash].pub
          /\ ledger[n][prevHash].type # "Genesis"
    /\ LET newHash == CalculateHash([type |-> "Send",
                                     prev |-> lastHash,
                                     dest |-> to,
                                     repr |-> NoBlock,
                                     amount |-> amt,
                                     sig   |-> ledger[n][lastHash].pub,
                                     pub   |-> ledger[n][lastHash].pub],
                                    lastHash) IN
       /\ lastHash' = newHash
       /\ ledger' = [node \in Node |-> 
                      [h \in Hash |-> 
                         IF h = newHash THEN
                             [type |-> "Send",
                              prev |-> lastHash,
                              dest |-> to,
                              repr |-> NoBlock,
                              amount |-> amt,
                              sig   |-> ledger[n][lastHash].pub,
                              pub   |-> ledger[n][lastHash].pub]
                         ELSE ledger[node][h]]]
       /\ received' = [node \in Node |-> received[node] \cup {newHash}]

CreateOpen(n, sendHash) ==
    /\ n \in Node
    /\ sendHash \in Hash
    /\ ledger[n][sendHash].type = "Send"
    /\ ledger[n][sendHash].dest = ledger[n][sendHash].pub   \* dest matches this account's public key
    /\ LET newHash == CalculateHash([type |-> "Open",
                                     prev |-> NoHash,
                                     dest |-> NoBlock,
                                     repr |-> NoBlock,
                                     amount |-> ledger[n][sendHash].amount,
                                     sig   |-> ledger[n][sendHash].dest,
                                     pub   |-> ledger[n][sendHash].dest],
                                    NoHash) IN
       /\ lastHash' = newHash
       /\ ledger' = [node \in Node |-> 
                      [h \in Hash |-> 
                         IF h = newHash THEN
                             [type |-> "Open",
                              prev |-> NoHash,
                              dest |-> NoBlock,
                              repr |-> NoBlock,
                              amount |-> ledger[n][sendHash].amount,
                              sig   |-> ledger[n][sendHash].dest,
                              pub   |-> ledger[n][sendHash].dest]
                         ELSE ledger[node][h]]]
       /\ received' = [node \in Node |-> received[node] \cup {newHash}]

CreateReceive(n, sendHash) ==
    /\ n \in Node
    /\ sendHash \in Hash
    /\ ledger[n][sendHash].type = "Send"
    /\ ledger[n][sendHash].dest = ledger[n][lastHash].pub   \* block belongs to this account
    /\ LET newHash == CalculateHash([type |-> "Receive",
                                     prev |-> lastHash,
                                     dest |-> NoBlock,
                                     repr |-> NoBlock,
                                     amount |-> ledger[n][sendHash].amount,
                                     sig   |-> ledger[n][lastHash].pub,
                                     pub   |-> ledger[n][lastHash].pub],
                                    lastHash) IN
       /\ lastHash' = newHash
       /\ ledger' = [node \in Node |-> 
                      [h \in Hash |-> 
                         IF h = newHash THEN
                             [type |-> "Receive",
                              prev |-> lastHash,
                              dest |-> NoBlock,
                              repr |-> NoBlock,
                              amount |-> ledger[n][sendHash].amount,
                              sig   |-> ledger[n][lastHash].pub,
                              pub   |-> ledger[n][lastHash].pub]
                         ELSE ledger[node][h]]]
       /\ received' = [node \in Node |-> received[node] \cup {newHash}]

CreateChange(n, newRepr) ==
    /\ n \in Node
    /\ newRepr \in Account
    /\ LET newHash == CalculateHash([type |-> "Change",
                                     prev |-> lastHash,
                                     dest |-> NoBlock,
                                     repr |-> newRepr,
                                     amount |-> NoBlock,
                                     sig   |-> ledger[n][lastHash].pub,
                                     pub   |-> ledger[n][lastHash].pub],
                                    lastHash) IN
       /\ lastHash' = newHash
       /\ ledger' = [node \in Node |-> 
                      [h \in Hash |-> 
                         IF h = newHash THEN
                             [type |-> "Change",
                              prev |-> lastHash,
                              dest |-> NoBlock,
                              repr |-> newRepr,
                              amount |-> NoBlock,
                              sig   |-> ledger[n][lastHash].pub,
                              pub   |-> ledger[n][lastHash].pub]
                         ELSE ledger[node][h]]]
       /\ received' = [node \in Node |-> received[node] \cup {newHash}]

ProcessReceived(n) ==
    /\ n \in Node
    /\ \E h \in received[n] :
          /\ ledger[n][h] = NoBlock
          /\ LET b == h IN
               /\ ValidateBlock(n, ledger[n][lastHash].pub, h)
          /\ ledger' = [node \in Node |-> 
                        [hash \in Hash |-> 
                           IF node = n /\ hash = h THEN
                               (* Assume we can reconstruct the block from the hash;
                                  in practice the block would be transmitted fully *)
                               ledger[node][lastHash]   \* placeholder: use last block as content
                           ELSE ledger[node][hash]]]
          /\ received' = [node \in Node |-> 
                           IF node = n THEN received[node] \ {h}
                           ELSE received[node]]
          /\ UNCHANGED lastHash

\* Placeholder signature validation (abstract, always true for model)
ValidateBlock(n, acctPub, h) == TRUE

\* ----------------------------------------------------------------------
\* Next-state relation (union of all possible actions)
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ \E n \in Node, to \in Account, amt \in Nat : CreateSend(n, to, amt)
    \/ \E n \in Node, sh \in Hash : CreateOpen(n, sh)
    \/ \E n \in Node, sh \in Hash : CreateReceive(n, sh)
    \/ \E n \in Node, r \in Account   : CreateChange(n, r)
    \/ \E n \in Node : ProcessReceived(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in HashSet \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET HashSet]

\* Cryptographic (signature) invariant: every block present has sig equal to its owner's pub key
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        LET b == ledger[n][h] IN
        (b = NoBlock) \/ (b.sig = b.pub)

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====