---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the .cfg file.
-----------------------------------------------------------------*)
CONSTANTS
    Hash,               \* Set of possible block hashes
    NoHashVal,          \* Sentinel value meaning “no previous hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value meaning “empty slot in the ledger”
    NoHash,             \* Alias for NoHashVal (also used in the spec)
    NoBlock,            \* Alias for NoBlockVal
    PrivateToPublic,    \* Mapping from a private key to its public key
    CalculateHashImpl   \* Abstract hash calculation (overridden in .cfg)

(*-----------------------------------------------------------------
  Types and record definition for a block.
-----------------------------------------------------------------*)
Block ==
    [ type     : {"genesis", "send", "receive", "open", "change"},
      prev     : Hash \cup {NoHash},
      account  : PublicKey,
      dest     : PublicKey,
      amount   : Nat,
      sigKey   : PrivateKey,
      hash     : Hash ]

(*-----------------------------------------------------------------
  Helper predicates.
-----------------------------------------------------------------*)
IsNoHash(h) == h = NoHash
IsNoBlock(b) == b = NoBlock

ValidSignature(b) ==
    /\ b.sigKey \in PrivateKey
    /\ PrivateToPublic[b.sigKey] = b.account

PrevExists(b, l) ==
    IF b.prev = NoHash THEN TRUE
    ELSE \E n \in Node : l[n][b.prev] # NoBlock

ValidateBlock(b, l) ==
    /\ ValidSignature(b)
    /\ PrevExists(b, l)
    (* Additional block‑type‑specific checks are omitted for brevity. *)

(*-----------------------------------------------------------------
  Placeholder for hash calculation; will be overridden by the
  configuration (CalculateHashImpl).
-----------------------------------------------------------------*)
CalculateHash(b, p) == CalculateHashImpl(b, p)

(*-----------------------------------------------------------------
  State variables.
-----------------------------------------------------------------*)
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* ledger[n][h] = block stored at node n under hash h, or NoBlock
    received,   \* received[n] = set of hashes that node n has seen but not yet processed
    pending,    \* pending[h] = block that has been created but not yet stored permanently
    genesisCreated \* Boolean flag indicating whether the genesis block has been created

(*-----------------------------------------------------------------
  Initial state.
-----------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]
    /\ pending = [ h \in Hash |-> NoBlock ]
    /\ genesisCreated = FALSE

(*-----------------------------------------------------------------
  Action: create a new block (any type).  The block is added to the
  global pending map and broadcast to every node’s received set.
-----------------------------------------------------------------*)
CreateBlock(b) ==
    LET h == CalculateHash(b, lastHash) IN
    /\ h \in Hash
    /\ b.type \in {"genesis", "send", "receive", "open", "change"}
    /\ b.prev \in Hash \cup {NoHash}
    /\ b.account \in PublicKey
    /\ b.dest \in PublicKey
    /\ b.amount \in Nat
    /\ b.sigKey \in PrivateKey
    /\ b.hash = h
    /\ ValidSignature(b)
    /\ IF b.type = "genesis" THEN ~genesisCreated ELSE TRUE
    /\ pending' = [ pending EXCEPT ![h] = b ]
    /\ lastHash' = h
    /\ received' = [ n \in Node |-> received[n] \cup {h} ]
    /\ genesisCreated' = IF b.type = "genesis" THEN TRUE ELSE genesisCreated
    /\ UNCHANGED ledger

(*-----------------------------------------------------------------
  Action: a node processes one of the blocks it has received.
-----------------------------------------------------------------*)
ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
          LET b == pending[h] IN
          /\ b # NoBlock
          /\ ValidateBlock(b, ledger)
          /\ ledger' = [ ledger EXCEPT ![node][h] = b ]
          /\ received' = [ received EXCEPT ![node] = received[node] \ {h} ]
          /\ UNCHANGED <<lastHash, pending, genesisCreated>>

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next ==
    \/ \E b \in Block : CreateBlock(b)
    \/ \E n \in Node : ProcessBlock(n)

(*-----------------------------------------------------------------
  Specification.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<lastHash, ledger, received, pending, genesisCreated>>

(*-----------------------------------------------------------------
  Invariants.
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ pending \in [Hash -> (Block \cup {NoBlock})]
    /\ genesisCreated \in BOOLEAN

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlock
            THEN ValidSignature(ledger[n][h])
            ELSE TRUE
====