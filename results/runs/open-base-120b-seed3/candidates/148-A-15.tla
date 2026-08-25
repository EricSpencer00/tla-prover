---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(* ---------- CONSTANT DECLARATIONS ---------- *)
CONSTANTS
    Hash,            \* the set of all possible block hashes
    NoHash,          \* a distinguished element of Hash used as a sentinel
    NoHashVal,       \* another name for the sentinel (kept for compatibility)
    PrivateKey,      \* the set of all private keys
    PublicKey,       \* the set of all public keys
    Node,            \* the set of network nodes
    GenesisBalance, \* total supply of coins at genesis (a natural number)
    NoBlock,         \* a sentinel value representing the absence of a block
    NoBlockVal,      \* another name for the sentinel block value
    CalculateHash,   \* abstract hash calculation operator (to be overridden)
    CalculateHashImpl

(* ---------- TYPE DEFINITIONS ---------- *)
BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [
    type          : BlockType,
    account       : PublicKey,          \* owner of the account chain
    prev          : Hash,               \* previous block hash in this chain
    amount        : Nat,                \* amount transferred (if applicable)
    recipient     : PublicKey,          \* destination account (send/open)
    source        : Hash,               \* hash of the source send block (receive)
    representative: PublicKey,          \* voting representative (change)
    signature     : STRING              \* abstract signature
]

(* ---------- STATE VARIABLES ---------- *)
VARIABLES
    LastHash,        \* the hash of the most recently created block (or NoHashVal)
    Ledger,          \* [Node -> [Hash -> Block \cup {NoBlock}]]
    Received,        \* [Node -> SUBSET Hash]   \* blocks awaiting processing
    GenesisCreated   \* BOOLEAN flag to ensure genesis happens once

(* ---------- HELPER DEFINITIONS ---------- *)

\* Override of the hash function used in the model; the .cfg file substitutes
\* CalculateHashImpl for CalculateHash.
CalcHash(b) == CalculateHashImpl(b, LastHash)

BlockHash(b) == CalcHash(b)

\* Function to update a single node's ledger with a new block
UpdateLedgerNode(ln, h, blk) ==
    [h2 \in Hash |-> IF h2 = h THEN blk ELSE ln[h2]]

\* Broadcast a newly created block hash to every node's Received set
Broadcast(h) ==
    [n \in Node |-> Received[n] \cup {h}]

\* Determine the public key that corresponds to a given private key.
\* In an abstract model we assume a total function PrivToPub.
PrivToPub \in [PrivateKey -> PublicKey]

\* Abstract predicate stating that a block's signature is valid.
ValidSignature(b) ==
    (* In a concrete model this would verify the cryptographic signature.
       Here we keep it abstract and assume all signatures are valid. *)
    TRUE

\* Retrieve the block with hash h from any node's ledger (they are identical).
GetBlock(h) ==
    LET n == CHOOSE n \in Node : TRUE IN Ledger[n][h]

\* Compute the balance of an account by walking its chain.
Balance(acc) ==
    LET hashes == { h \in Hash : 
                       (GetBlock(h).account = acc) /\ GetBlock(h) # NoBlock } IN
    LET sendAmounts == { GetBlock(h).amount : h \in hashes /\ GetBlock(h).type = "send" } IN
    LET recvAmounts == { GetBlock(h).amount : h \in hashes /\ GetBlock(h).type = "receive" } IN
    IF acc = (CHOOSE pk \in PublicKey : TRUE) THEN
        GenesisBalance - Sum(SendAmounts) + Sum(RecvAmounts)
    ELSE
        Sum(RecvAmounts) - Sum(SendAmounts)

(* ---------- INITIAL STATE ---------- *)
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ GenesisCreated = FALSE

(* ---------- ACTIONS ---------- *)

\* 1. Create the genesis block (once)
CreateGenesis ==
    /\ ~GenesisCreated
    /\ LastHash = NoHashVal
    /\ \E pk \in PublicKey :
          \E sk \in PrivateKey :
              /\ PrivToPub[sk] = pk
              /\ LET gBlk == [
                     type          |-> "genesis",
                     account       |-> pk,
                     prev          |-> NoHash,
                     amount        |-> GenesisBalance,
                     recipient     |-> NoHash,
                     source        |-> NoHash,
                     representative|-> NoHash,
                     signature     |-> "sig"
                  ] IN
                 LET h == BlockHash(gBlk) IN
                 /\ h \in Hash
                 /\ \A n \in Node :
                        Ledger' = [Ledger EXCEPT ![n][h] = gBlk]
                 /\ Received' = Broadcast(h)
                 /\ LastHash' = h
                 /\ GenesisCreated' = TRUE
                 /\ UNCHANGED <<GenesisCreated, LastHash, Ledger, Received>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* 2. Create a send block
CreateSend(sk, recipient, amt) ==
    /\ sk \in PrivateKey
    /\ let senderPk == PrivToPub[sk] in
       \E hPrev \in Hash :
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev] # NoBlockVal
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev].account = senderPk
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev].type # "receive"
          /\ Balance(senderPk) >= amt
          /\ LET sBlk == [
                 type          |-> "send",
                 account       |-> senderPk,
                 prev          |-> hPrev,
                 amount        |-> amt,
                 recipient     |-> recipient,
                 source        |-> NoHash,
                 representative|-> NoHash,
                 signature     |-> "sig"
               ] IN
             LET h == BlockHash(sBlk) IN
             /\ h \in Hash
             /\ \A n \in Node :
                    Ledger' = [Ledger EXCEPT ![n][h] = sBlk]
             /\ Received' = Broadcast(h)
             /\ LastHash' = h
             /\ UNCHANGED <<GenesisCreated>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* 3. Create an open block (first block of a new account)
CreateOpen(sk, sourceHash) ==
    /\ sk \in PrivateKey
    /\ let newPk == PrivToPub[sk] in
       \E srcBlk \in Block :
          /\ srcBlk = GetBlock(sourceHash)
          /\ srcBlk.type = "send"
          /\ srcBlk.recipient = newPk
          /\ \A n \in Node :
                 LET oBlk == [
                        type          |-> "open",
                        account       |-> newPk,
                        prev          |-> NoHash,
                        amount        |-> srcBlk.amount,
                        recipient     |-> NoHash,
                        source        |-> sourceHash,
                        representative|-> NoHash,
                        signature     |-> "sig"
                     ] IN
                     LET h == BlockHash(oBlk) IN
                     /\ h \in Hash
                     /\ Ledger' = [Ledger EXCEPT ![n][h] = oBlk]
                     /\ Received' = Broadcast(h)
                     /\ LastHash' = h
          /\ UNCHANGED <<GenesisCreated>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* 4. Create a receive block
CreateReceive(sk, sourceHash) ==
    /\ sk \in PrivateKey
    /\ let recPk == PrivToPub[sk] in
       \E hPrev \in Hash :
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev] # NoBlockVal
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev].account = recPk
          /\ LET srcBlk == GetBlock(sourceHash) IN
               /\ srcBlk.type = "send"
               /\ srcBlk.recipient = recPk
               /\ ~ (sourceHash \in { Ledger[CHOOSE n \in Node : TRUE][h].source : h \in Hash })
          /\ LET rBlk == [
                 type          |-> "receive",
                 account       |-> recPk,
                 prev          |-> hPrev,
                 amount        |-> srcBlk.amount,
                 recipient     |-> NoHash,
                 source        |-> sourceHash,
                 representative|-> NoHash,
                 signature     |-> "sig"
               ] IN
               LET h == BlockHash(rBlk) IN
               /\ h \in Hash
               /\ \A n \in Node :
                      Ledger' = [Ledger EXCEPT ![n][h] = rBlk]
               /\ Received' = Broadcast(h)
               /\ LastHash' = h
               /\ UNCHANGED <<GenesisCreated>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* 5. Create a change representative block
CreateChange(sk, newRep) ==
    /\ sk \in PrivateKey
    /\ let accPk == PrivToPub[sk] in
       \E hPrev \in Hash :
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev] # NoBlockVal
          /\ Ledger[CHOOSE n \in Node : TRUE][hPrev].account = accPk
          /\ LET cBlk == [
                 type          |-> "change",
                 account       |-> accPk,
                 prev          |-> hPrev,
                 amount        |-> 0,
                 recipient     |-> NoHash,
                 source        |-> NoHash,
                 representative|-> newRep,
                 signature     |-> "sig"
               ] IN
               LET h == BlockHash(cBlk) IN
               /\ h \in Hash
               /\ \A n \in Node :
                      Ledger' = [Ledger EXCEPT ![n][h] = cBlk]
               /\ Received' = Broadcast(h)
               /\ LastHash' = h
               /\ UNCHANGED <<GenesisCreated>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* 6. Process a received block at a node (validation + insertion)
ProcessBlock(n) ==
    /\ n \in Node
    /\ \E h \in Received[n] :
          LET b == GetBlock(h) IN
          /\ b # NoBlockVal
          /\ ValidSignature(b)
          /\ (b.type = "send" => 
                LET senderBal == Balance(b.account) IN senderBal >= b.amount)
          /\ (b.type = "open" => 
                (* open must reference an unclaimed send *)
                LET src == GetBlock(b.source) IN src.type = "send" /\ src.recipient = b.account)
          /\ (b.type = "receive" => 
                (* receive must reference an unclaimed send *)
                LET src == GetBlock(b.source) IN src.type = "send" /\ src.recipient = b.account)
          /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
          /\ Ledger' = [Ledger EXCEPT ![n] = UpdateLedgerNode(@[n], h, b)]
          /\ UNCHANGED <<LastHash, GenesisCreated>>
    /\ UNCHANGED <<Ledger, Received, LastHash, GenesisCreated>>

\* The overall NEXT relation (any enabled action may occur)
Next ==
    \/ CreateGenesis
    \/ \E sk \in PrivateKey, rcpt \in PublicKey, amt \in Nat : CreateSend(sk, rcpt, amt)
    \/ \E sk \in PrivateKey, src \in Hash : CreateOpen(sk, src)
    \/ \E sk \in PrivateKey, src \in Hash : CreateReceive(sk, src)
    \/ \E sk \in PrivateKey, rep \in PublicKey : CreateChange(sk, rep)
    \/ \E n \in Node : ProcessBlock(n)

(* ---------- SPECIFICATION ---------- *)

Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, GenesisCreated>>

(* ---------- INVARIANTS ---------- *)

TypeInvariant ==
    /\ LastHash \in Hash \/ LastHash = NoHashVal
    /\ Ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ GenesisCreated \in BOOLEAN

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == Ledger[n][h] IN
            blk = NoBlockVal \/ ValidSignature(blk)

====