---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning “no previous hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value meaning “no block stored”
    CalculateHash,      \* Abstract hash function (overridden by CalculateHashImpl)
    NoHash,             \* Alias for NoHashVal (sentinel hash)
    NoBlock,            \* Alias for NoBlockVal (sentinel block)

\* ----------------------------------------------------------------------
\* USER‑DEFINED CONSTANTS (can be defined in the cfg or left abstract)
\* ----------------------------------------------------------------------
\* Mapping from each private key to its public key
CONSTANT PrivToPub \in [PrivateKey -> PublicKey]

\* Mapping from each node to the private key it owns
CONSTANT NodePriv   \in [Node -> PrivateKey]

\* Public key of the genesis account (derived from a private key)
CONSTANT GenesisPriv \in PrivateKey
CONSTANT GenesisPub  == PrivToPub[GenesisPriv]

\* ----------------------------------------------------------------------
\* ALIASES
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* BLOCK REPRESENTATION
\* ----------------------------------------------------------------------
Block ==
    [ type    : {"genesis","send","open","receive","change"},
      hash    : Hash,
      prev    : Hash,
      acct    : PublicKey,        \* owner of the chain this block belongs to
      dest    : PublicKey,        \* for send/open/receive (NoHash if unused)
      amount  : Nat,              \* amount of nano transferred (0 if unused)
      rep     : PublicKey,        \* new representative (NoHash if unused)
      signer  : PrivateKey,       \* private key that signed the block
      sig     : Sig               \* signature artefact
    ]

\* ----------------------------------------------------------------------
\* SIGNATURE MODEL (highly abstract)
\* ----------------------------------------------------------------------
Sig == UNION {<<priv, data>> : priv \in PrivateKey,
                            data \in Seq(BOOLEAN)}  \* abstract datatype

Data(b) == << b.type , b.prev , b.acct , b.dest , b.amount , b.rep >>

Sign(priv, d) == << priv , d >>

ValidSignature(b) ==
    /\ b.sig = Sign(b.signer, Data(b))
    /\ PrivToPub[b.signer] = b.acct

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,      \* The most recent hash that has been calculated globally
    Ledger,        \* [Node -> [Hash -> Block \/ NoBlockVal]]
    Received,      \* [Node -> SUBSET Hash]  (blocks waiting to be processed)
    BlockStore     \* [Hash -> Block \/ NoBlockVal]  (global repository of created blocks)

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ]]
    /\ Received = [ n \in Node |-> {} ]
    /\ BlockStore = [ h \in Hash |-> NoBlock ]

\* ----------------------------------------------------------------------
\* HELPERS
\* ----------------------------------------------------------------------
HashOf(b) == b.hash

\* For the purpose of this abstract model we treat balances loosely.
\* A precise recursive balance computation would be far more involved.
\* Here we only require that a send block does not transfer more than
\* the total genesis balance – a safe over‑approximation.
SendAmountOk(b) ==
    b.type = "send" => b.amount <= GenesisBalance

\* ----------------------------------------------------------------------
\* ACTION: CREATE GENESIS BLOCK (can happen only once)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ LastHash = NoHash               \* no block has been created yet
    /\ LET
          d == << "genesis", NoHash, GenesisPub, NoHash, GenesisBalance, NoHash >>
          h == CalculateHash(d, NoHash)
          b == [ type    |-> "genesis",
                hash    |-> h,
                prev    |-> NoHash,
                acct    |-> GenesisPub,
                dest    |-> NoHash,
                amount  |-> GenesisBalance,
                rep     |-> NoHash,
                signer  |-> GenesisPriv,
                sig     |-> Sign(GenesisPriv, d) ]
       IN
          /\ LastHash' = h
          /\ BlockStore' = [BlockStore EXCEPT ![h] = b]
          /\ Ledger' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE Ledger[n][h2] ] ]
          /\ Received' = Received
    /\ UNCHANGED <<>>   \* no other variables

\* ----------------------------------------------------------------------
\* ACTION: CREATE SEND BLOCK
\* ----------------------------------------------------------------------
CreateSend ==
    /\ \E n \in Node :
          LET
              priv == NodePriv[n]
              pub  == PrivToPub[priv]
              \* Choose a destination public key (different from sender)
              dest \in PublicKey \ {pub}
              amt  \in Nat
              prevHash == LastHash
              d == << "send", prevHash, pub, dest, amt, NoHash >>
              h == CalculateHash(d, prevHash)
              b == [ type    |-> "send",
                    hash    |-> h,
                    prev    |-> prevHash,
                    acct    |-> pub,
                    dest    |-> dest,
                    amount  |-> amt,
                    rep     |-> NoHash,
                    signer  |-> priv,
                    sig     |-> Sign(priv, d) ]
           IN
              /\ SendAmountOk(b)               \* (over‑approximation)
              /\ LastHash' = h
              /\ BlockStore' = [BlockStore EXCEPT ![h] = b]
              /\ Received' = [ r \in Node |-> IF r = n THEN @ \cup {h} ELSE @ ]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>   \* no other variables

\* ----------------------------------------------------------------------
\* ACTION: CREATE OPEN BLOCK (opening a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node :
          LET
              priv == NodePriv[n]
              pub  == PrivToPub[priv]
              \* The send block that funds this account must already exist
              srcHash \in DOMAIN BlockStore
              srcBlk  == BlockStore[srcHash]
              /\ srcBlk.type = "send"
              /\ srcBlk.dest = pub
              prevHash == NoHash               \* first block of this chain
              d == << "open", prevHash, pub, NoHash, srcBlk.amount, NoHash >>
              h == CalculateHash(d, prevHash)
              b == [ type    |-> "open",
                    hash    |-> h,
                    prev    |-> prevHash,
                    acct    |-> pub,
                    dest    |-> NoHash,
                    amount  |-> srcBlk.amount,
                    rep     |-> NoHash,
                    signer  |-> priv,
                    sig     |-> Sign(priv, d) ]
           IN
              /\ LastHash' = h
              /\ BlockStore' = [BlockStore EXCEPT ![h] = b]
              /\ Received' = [ r \in Node |-> IF r = n THEN @ \cup {h} ELSE @ ]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE RECEIVE BLOCK
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node :
          LET
              priv == NodePriv[n]
              pub  == PrivToPub[priv]
              \* Choose a send block that is pending receipt
              srcHash \in DOMAIN BlockStore
              srcBlk  == BlockStore[srcHash]
              /\ srcBlk.type = "send"
              /\ srcBlk.dest = pub
              prevHash == LastHash
              d == << "receive", prevHash, pub, srcHash, srcBlk.amount, NoHash >>
              h == CalculateHash(d, prevHash)
              b == [ type    |-> "receive",
                    hash    |-> h,
                    prev    |-> prevHash,
                    acct    |-> pub,
                    dest    |-> srcHash,
                    amount  |-> srcBlk.amount,
                    rep     |-> NoHash,
                    signer  |-> priv,
                    sig     |-> Sign(priv, d) ]
           IN
              /\ LastHash' = h
              /\ BlockStore' = [BlockStore EXCEPT ![h] = b]
              /\ Received' = [ r \in Node |-> IF r = n THEN @ \cup {h} ELSE @ ]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE CHANGE REPRESENTATIVE BLOCK
\* ----------------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node :
          LET
              priv == NodePriv[n]
              pub  == PrivToPub[priv]
              newRep \in PublicKey
              prevHash == LastHash
              d == << "change", prevHash, pub, NoHash, 0, newRep >>
              h == CalculateHash(d, prevHash)
              b == [ type    |-> "change",
                    hash    |-> h,
                    prev    |-> prevHash,
                    acct    |-> pub,
                    dest    |-> NoHash,
                    amount  |-> 0,
                    rep     |-> newRep,
                    signer  |-> priv,
                    sig     |-> Sign(priv, d) ]
           IN
              /\ LastHash' = h
              /\ BlockStore' = [BlockStore EXCEPT ![h] = b]
              /\ Received' = [ r \in Node |-> IF r = n THEN @ \cup {h} ELSE @ ]
              /\ UNCHANGED <<Ledger>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* ACTION: PROCESS A RECEIVED BLOCK
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
          /\ \E h \in Received[n] :
                LET b == BlockStore[h] IN
                /\ b # NoBlock
                /\ ValidSignature(b)                 \* cryptographic check
                /\ (* reference existence check *)
                   (b.prev = NoHash \/ BlockStore[b.prev] # NoBlock)
                /\ (* simple type‑specific checks *)
                   IF b.type = "send" THEN
                       SendAmountOk(b)
                   ELSE TRUE
                /\ Ledger' = [ Ledger EXCEPT ![n][h] = b ]
                /\ Received' = [ Received EXCEPT ![n] = @ \ {h} ]
                /\ UNCHANGED <<LastHash, BlockStore>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* STATE VARIABLE TUPLE
\* ----------------------------------------------------------------------
vars == <<LastHash, Ledger, Received, BlockStore>>

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger \in [Node -> [Hash -> (Block \/ NoBlock)]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ BlockStore \in [Hash -> (Block \/ NoBlock)]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic validity of every stored block)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in DOMAIN Ledger[n] :
            LET b == Ledger[n][h] IN
                IF b = NoBlock THEN TRUE ELSE ValidSignature(b)

\* ----------------------------------------------------------------------
\* CONFIGURATION SUBSTITUTION: CALCULATEHASH IMPLEMENTATION
\* ----------------------------------------------------------------------
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* Dummy finite implementation for model checking (to be overridden)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====