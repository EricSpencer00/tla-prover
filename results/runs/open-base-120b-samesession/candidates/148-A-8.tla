---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,           \* Set of possible block hashes
    NoHashVal,      \* Sentinel value for a non‑existent hash (may be equal to NoHash)
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,           \* Set of network nodes
    GenesisBalance,\* Total number of coins at genesis (a natural number)
    NoBlockVal,    \* Sentinel value for an empty block slot
    CalculateHash, \* Abstract hash operator (will be overridden by CalculateHashImpl in the cfg)
    NoHash,        \* Distinct sentinel hash not belonging to Hash
    NoBlock        \* Distinct sentinel hash for a non‑existent block

\* ----------------------------------------------------------------------
\* Additional constant definitions required for the model
\* ----------------------------------------------------------------------
ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash
ASSUME NoHashVal = NoHash
ASSUME NoBlockVal = NoBlock

\* Mapping from a private key to its public counterpart
CONSTANT PrivateToPublic \in [PrivateKey -> PublicKey]

\* Mapping from a node to the private key it owns
CONSTANT NodeKey \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block ==
    [ type      : {"genesis", "send", "open", "receive", "change", "none"},
      prevHash  : Hash \/ {NoHash},
      account   : PublicKey,
      signature : STRING,
      amount    : Nat,
      dest      : PublicKey,   \* destination for send/open blocks
      source    : Hash \/ {NoHash} ]   \* referenced send block for receive/open

\* ----------------------------------------------------------------------
\* Helper operators
\* ----------------------------------------------------------------------
PublicOf(node) == PrivateToPublic[NodeKey[node]]

ValidSignature(b) ==
    /\ b.signature = b.account    \* abstract signature check: signature equals account key
    /\ b.account \in PublicKey

\* Balance of an account is defined recursively by walking the chain.
\* For the purpose of this specification we provide a simple over‑approximation:
\* a node may create a send block with any amount not exceeding GenesisBalance.
\* A precise recursive definition could be added later.
CanSend(node, amt) ==
    amt <= GenesisBalance

\* ----------------------------------------------------------------------
\* Abstract hash calculation implementation (to be substituted for CalculateHash)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,   \* The most recent block hash used for ordering (or NoHash)
    Ledger,     \* [Node -> [Hash -> Block]]  each node’s copy of the ledger
    Received,   \* [Node -> SUBSET Hash]      blocks received but not yet validated
    Blocks      \* [Hash -> Block]            globally known blocks (including sent ones)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ Blocks = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ LastHash = NoHash                                   \* only once
    /\ \E n \in Node :
          LET pk == PublicOf(n)
              blk == [ type      |-> "genesis",
                       prevHash  |-> NoHash,
                       account   |-> pk,
                       signature |-> pk,
                       amount    |-> GenesisBalance,
                       dest      |-> "",
                       source    |-> NoHash ]
              h   == CalculateHash(blk, NoHash)            \* will be replaced by CalculateHashImpl
          IN
              /\ h \in Hash
              /\ Blocks' = [Blocks EXCEPT ![h] = blk]
              /\ LastHash' = h
              /\ Ledger' = [m \in Node |-> [h' \in Hash |-> IF h' = h THEN blk ELSE Ledger[m][h']]]
              /\ Received' = [m \in Node |-> Received[m]]
              /\ UNCHANGED <<>>   \* no other variables
    /\ UNCHANGED <<>>   \* ensures only one node can fire this action

CreateSend ==
    /\ LastHash # NoHash
    /\ \E n \in Node, amt \in Nat :
          LET pk == PublicOf(n)
              blk == [ type      |-> "send",
                       prevHash  |-> LastHash,
                       account   |-> pk,
                       signature |-> pk,
                       amount    |-> amt,
                       dest      |-> "",          \* destination to be filled by higher‑level spec
                       source    |-> NoHash ]
              h   == CalculateHash(blk, LastHash)
          IN
              /\ amt > 0
              /\ CanSend(n, amt)
              /\ h \in Hash
              /\ Blocks' = [Blocks EXCEPT ![h] = blk]
              /\ LastHash' = h
              /\ Received' = [m \in Node |-> Received[m] \cup {h}]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>   \* no other variables

CreateOpen ==
    /\ LastHash # NoHash
    /\ \E n \in Node, src \in Hash :
          LET pk == PublicOf(n)
              blk == [ type      |-> "open",
                       prevHash  |-> NoHash,
                       account   |-> pk,
                       signature |-> pk,
                       amount    |-> 0,
                       dest      |-> "",
                       source    |-> src ]
              h   == CalculateHash(blk, LastHash)
          IN
              /\ src \in Hash
              /\ Blocks[src] # NoBlockVal                \* referenced send block must exist
              /\ h \in Hash
              /\ Blocks' = [Blocks EXCEPT ![h] = blk]
              /\ LastHash' = h
              /\ Received' = [m \in Node |-> Received[m] \cup {h}]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

CreateReceive ==
    /\ LastHash # NoHash
    /\ \E n \in Node, src \in Hash :
          LET pk == PublicOf(n)
              blk == [ type      |-> "receive",
                       prevHash  |-> LastHash,
                       account   |-> pk,
                       signature |-> pk,
                       amount    |-> 0,
                       dest      |-> "",
                       source    |-> src ]
              h   == CalculateHash(blk, LastHash)
          IN
              /\ src \in Hash
              /\ Blocks[src] # NoBlockVal                \* referenced send block must exist
              /\ h \in Hash
              /\ Blocks' = [Blocks EXCEPT ![h] = blk]
              /\ LastHash' = h
              /\ Received' = [m \in Node |-> Received[m] \cup {h}]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

CreateChange ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
          LET pk == PublicOf(n)
              blk == [ type      |-> "change",
                       prevHash  |-> LastHash,
                       account   |-> pk,
                       signature |-> pk,
                       amount    |-> 0,
                       dest      |-> "",
                       source    |-> NoHash ]
              h   == CalculateHash(blk, LastHash)
          IN
              /\ h \in Hash
              /\ Blocks' = [Blocks EXCEPT ![h] = blk]
              /\ LastHash' = h
              /\ Received' = [m \in Node |-> Received[m] \cup {h}]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Block processing (validation) action
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node, h \in Received[n] :
          LET b == Blocks[h]
          IN
              /\ b # NoBlockVal
              /\ ValidSignature(b)
              /\ \* Additional type‑specific checks could be added here
                 Ledger' = [Ledger EXCEPT ![n][h] = b]
              /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
              /\ UNCHANGED <<LastHash, Blocks>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, Blocks>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ {NoHash}
    /\ Ledger \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ Blocks \in [Hash -> Block]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF Ledger[n][h] # NoBlockVal
            THEN ValidSignature(Ledger[n][h])
            ELSE TRUE

====