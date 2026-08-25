---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel value for \"no hash\"
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total amount of coins at genesis (natural number)
    NoBlockVal,      \* Sentinel value for \"no block\"
    CalculateHash,   \* Abstract hash function (will be overridden by CalculateHashImpl)
    NoHash,          \* Alias for NoHashVal (sentinel for empty hash)
    NoBlock          \* Alias for NoBlockVal (sentinel for empty block)

\* ----------------------------------------------------------------------
\* Mappings that are supplied as constants (they can be instantiated in the
\* .cfg file)
\* ----------------------------------------------------------------------
PubKeyOf \in [PrivateKey -> PublicKey]   \* private‑to‑public key mapping
OwnerKey \in [Node -> PrivateKey]        \* each node owns exactly one private key

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the most recent block hash (or NoHash)
    ledgers,    \* per‑node mapping from hashes to blocks
    received,   \* per‑node set of hashes received but not yet processed
    BlockData   \* global mapping from a hash to the block data that created it

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [ type          : BlockType,
           prev          : Hash,
           account       : PublicKey,
           recipient     : PublicKey,
           amount        : Nat,
           representative: PublicKey,
           sig           : PrivateKey ]

\* Sentinels
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
CalculateHashImpl(data) ==
    (* For model checking we simply pick an arbitrary hash from the
       finite set Hash.  The .cfg file can replace this with a bounded
       implementation. *)
    CHOOSE h \in Hash : TRUE

CalculateHash(data) == CalculateHashImpl(data)

\* Retrieve the most recent block belonging to an account in a given ledger.
\* This is a very coarse approximation sufficient for the safety invariant.
LastBlockOfAccount(pk, ledger) ==
    IF \E h \in Hash : ledger[h] # NoBlock /\ ledger[h].account = pk
    THEN
        (* pick any block of the account – TLA+ does not enforce order here *)
        CHOOSE h \in Hash :
            ledger[h] # NoBlock /\ ledger[h].account = pk
    ELSE NoHash

\* Compute a (very) rough balance for an account from its ledger.
Balance(pk, ledger) ==
    IF \E h \in Hash : ledger[h] # NoBlock /\ ledger[h].account = pk
    THEN
        LET b == ledger[LastBlockOfAccount(pk, ledger)] IN
        CASE b.type = "genesis" -> b.amount
           [] b.type = "open"    -> b.amount
           [] b.type = "receive"-> b.amount
           [] b.type = "send"   -> 0
           [] b.type = "change" -> Balance(pk, ledger) \* unchanged
    ELSE 0

\* Verify that a block's signature matches the public key that owns the chain.
SignatureOK(b) ==
    PubKeyOf[b.sig] = b.account

\* Type‑specific validation rules (simplified).
ValidateBlock(b, ledger) ==
    /\ SignatureOK(b)
    /\ CASE b.type = "genesis" ->
            /\ b.prev = NoHash
            /\ b.amount = GenesisBalance
       [] b.type = "send" ->
            /\ b.prev # NoHash
            /\ b.amount <= Balance(b.account, ledger)
       [] b.type = "open" ->
            /\ b.prev = NoHash
            /\ b.amount > 0
       [] b.type = "receive" ->
            /\ b.prev # NoHash
            /\ b.amount > 0
       [] b.type = "change" ->
            /\ b.prev # NoHash
            /\ b.amount = 0

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ BlockData = [h \in Hash |-> NoBlock]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash                     \* only once
    /\ \A n \in Node: ledgers[n] = [h \in Hash |-> NoBlock]   \* all empty
    /\ let pk == PubKeyOf[OwnerKey[CHOOSE n \in Node : TRUE]] in
       let blk == [ type          |-> "genesis",
                    prev          |-> NoHash,
                    account       |-> pk,
                    recipient     |-> NoHash,
                    amount        |-> GenesisBalance,
                    representative|-> NoHash,
                    sig           |-> OwnerKey[CHOOSE n \in Node : TRUE] ] in
       let h == CalculateHash(blk) in
       /\ h \in Hash
       /\ BlockData' = [BlockData EXCEPT ![h] = blk]
       /\ lastHash' = h
       /\ \A n \in Node:
            ledgers' = [ledgers EXCEPT ![n][h] = blk]
       /\ received' = received
       /\ UNCHANGED <<>>   \* no other vars

CreateSend ==
    /\ \E n \in Node :
          LET pk == PubKeyOf[OwnerKey[n]] IN
          LET prev == LastBlockOfAccount(pk, ledgers[n]) IN
          prev # NoHash /\                  \* account must already exist
          \E amt \in Nat :
               amt <= Balance(pk, ledgers[n]) /\
               \E rcpt \in PublicKey :
                    LET blk == [ type          |-> "send",
                                 prev          |-> prev,
                                 account       |-> pk,
                                 recipient     |-> rcpt,
                                 amount        |-> amt,
                                 representative|-> NoHash,
                                 sig           |-> OwnerKey[n] ] IN
                    LET h == CalculateHash(blk) IN
                    /\ h \in Hash
                    /\ BlockData' = [BlockData EXCEPT ![h] = blk]
                    /\ lastHash' = h
                    /\ received' = [received EXCEPT ![m] = @ \cup {h} \* broadcast to all nodes
                                    \* (m ranges over all nodes)
                                    FOR m \in Node]
                    /\ UNCHANGED << ledgers >>
                    /\ UNCHANGED <<>>

CreateOpen ==
    /\ \E n \in Node :
          LET pk == PubKeyOf[OwnerKey[n]] IN
          /\ pk = pk   \* (trivial, just to bind pk)
          /\ \E sendHash \in Hash :
               /\ BlockData[sendHash].type = "send"
               /\ BlockData[sendHash].recipient = pk
               /\ BlockData[sendHash].account # pk   \* must be from another account
               LET blk == [ type          |-> "open",
                            prev          |-> NoHash,
                            account       |-> pk,
                            recipient     |-> NoHash,
                            amount        |-> BlockData[sendHash].amount,
                            representative|-> NoHash,
                            sig           |-> OwnerKey[n] ] IN
               LET h == CalculateHash(blk) IN
               /\ h \in Hash
               /\ BlockData' = [BlockData EXCEPT ![h] = blk]
               /\ lastHash' = h
               /\ received' = [received EXCEPT ![m] = @ \cup {h}
                               FOR m \in Node]
               /\ UNCHANGED << ledgers >>

CreateReceive ==
    /\ \E n \in Node :
          LET pk == PubKeyOf[OwnerKey[n]] IN
          LET prev == LastBlockOfAccount(pk, ledgers[n]) IN
          prev # NoHash /\               \* account must already be open
          /\ \E sendHash \in Hash :
               /\ BlockData[sendHash].type = "send"
               /\ BlockData[sendHash].recipient = pk
               /\ ~\E h \in Hash : ledgers[n][h] # NoBlock /\ h = sendHash   \* not yet claimed
               LET blk == [ type          |-> "receive",
                            prev          |-> prev,
                            account       |-> pk,
                            recipient     |-> NoHash,
                            amount        |-> BlockData[sendHash].amount,
                            representative|-> NoHash,
                            sig           |-> OwnerKey[n] ] IN
               LET h == CalculateHash(blk) IN
               /\ h \in Hash
               /\ BlockData' = [BlockData EXCEPT ![h] = blk]
               /\ lastHash' = h
               /\ received' = [received EXCEPT ![m] = @ \cup {h}
                               FOR m \in Node]
               /\ UNCHANGED << ledgers >>

CreateChange ==
    /\ \E n \in Node :
          LET pk == PubKeyOf[OwnerKey[n]] IN
          LET prev == LastBlockOfAccount(pk, ledgers[n]) IN
          prev # NoHash /\               \* must have a previous block
          /\ \E rep \in PublicKey :
               LET blk == [ type          |-> "change",
                            prev          |-> prev,
                            account       |-> pk,
                            recipient     |-> NoHash,
                            amount        |-> 0,
                            representative|-> rep,
                            sig           |-> OwnerKey[n] ] IN
               LET h == CalculateHash(blk) IN
               /\ h \in Hash
               /\ BlockData' = [BlockData EXCEPT ![h] = blk]
               /\ lastHash' = h
               /\ received' = [received EXCEPT ![m] = @ \cup {h}
                               FOR m \in Node]
               /\ UNCHANGED << ledgers >>

ProcessBlock ==
    /\ \E n \in Node :
          \E h \in received[n] :
               LET b == BlockData[h] IN
               /\ b # NoBlock
               /\ ValidateBlock(b, ledgers[n])
               /\ ledgers' = [ledgers EXCEPT ![n][h] = b]
               /\ received' = [received EXCEPT ![n] = @ \setminus {h}]
               /\ UNCHANGED << lastHash, BlockData >>

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
Spec == Init /\ [][Next]_<<lastHash, ledgers, received, BlockData>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledgers \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ BlockData \in [Hash -> Block]

SafetyInvariant ==
    /\ \A n \in Node :
         \A h \in Hash :
            IF ledgers[n][h] # NoBlock
            THEN PubKeyOf[ledgers[n][h].sig] = ledgers[n][h].account
            ELSE TRUE

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====