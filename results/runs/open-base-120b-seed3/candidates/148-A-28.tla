---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,         \* Universe of possible block hashes
    NoHashVal,    \* Sentinel hash value indicating no previous hash
    PrivateKey,  \* Set of all private keys
    PublicKey,   \* Set of all public keys
    Node,         \* Set of network nodes
    GenesisBalance, \* Total amount of coins created in the genesis block
    NoBlockVal,   \* Sentinel value representing the absence of a block
    CalculateHash, \* Abstract hash calculation operator (to be overridden)
    NoHash,       \* Alias for NoHashVal, used in the model
    NoBlock       \* Alias for NoBlockVal, used in the model

\* ----------------------------------------------------------------------
\* Aliases for the sentinel constants (they are required to be members of
\* the appropriate sets)
ASSUME NoHash \in Hash
ASSUME NoBlock \in {"genesis","send","open","receive","change"} \cup {NoBlockVal}

\* ----------------------------------------------------------------------
\* Mapping from a private key to its corresponding public key.
\* This is a constant function that the model checker may instantiate.
CONSTANT PrivToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Record type for a block.  Only the fields needed for the invariants are
\* modelled explicitly.
Block ==
    [ type       : {"genesis","send","open","receive","change"},
      account    : PublicKey,          \* Owner of the account chain
      previous   : Hash,               \* Hash of the previous block in the chain
      destination: PublicKey,          \* Recipient (for send/open/receive)
      amount     : Nat,                \* Amount of funds transferred
      signer     : PrivateKey ]        \* Private key used to sign the block

\* ----------------------------------------------------------------------
\* Abstract hash operator.  The concrete implementation is supplied via the
\* substitution operator CalculateHashImpl in the .cfg file.
CalculateHashImpl(data, prev) == 
    CHOOSE h \in Hash : TRUE   \* a placeholder; will be overridden

CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* Mapping: node -> (hash -> Block \/ NoBlock)
    received    \* Mapping: node -> set of hashes awaiting validation

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Helper to build a genesis block
GenesisBlock(sk) ==
    LET pk == PrivToPub[sk] IN
    [ type       |-> "genesis",
      account    |-> pk,
      previous   |-> NoHash,
      destination|-> NoHash,          \* not used for genesis
      amount     |-> GenesisBalance,
      signer     |-> sk ]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can occur only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E sk \in PrivateKey :
          LET b   == GenesisBlock(sk)                IN
          LET h   == CalculateHash(b, NoHash)        IN
          /\ h \in Hash
          /\ ledger' = [n \in Node |-> 
                         [hh \in Hash |-> 
                             IF hh = h THEN b ELSE ledger[n][hh]]]
          /\ lastHash' = h
          /\ UNCHANGED received

\* ----------------------------------------------------------------------
\* Action: process a received block (simplified – only moves the hash from the
\*         received set into the ledger without further checks)
ProcessReceived ==
    \E n \in Node :
        \E h \in received[n] :
            /\ ledger' = [n2 \in Node |-> 
                           IF n2 = n THEN
                               [hh \in Hash |-> 
                                   IF hh = h THEN 
                                       (* In a full model we would retrieve the block
                                          from a global block pool; here we just keep
                                          NoBlock to keep the model simple. *)
                                       NoBlock
                                   ELSE ledger[n][hh]]
                           ELSE ledger[n2]]
            /\ received' = [n2 \in Node |-> 
                             IF n2 = n THEN received[n] \ {h}
                             ELSE received[n2]]
            /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Stuttering step (allows the system to remain idle)
Stutter ==
    /\ UNCHANGED << lastHash, ledger, received >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ CreateGenesis
    \/ ProcessReceived
    \/ Stutter

\* ----------------------------------------------------------------------
\* Variable tuple for the temporal operator
vars == << lastHash, ledger, received >>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a signature that matches the
\* public key of the owning account.
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlock THEN
                LET b == ledger[n][h] IN
                PrivToPub[b.signer] = b.account
            ELSE TRUE

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The .cfg file will substitute a concrete implementation for CalculateHash.
\* The following operator is required by the configuration file.
CalculateHashImpl == CalculateHashImpl

====================