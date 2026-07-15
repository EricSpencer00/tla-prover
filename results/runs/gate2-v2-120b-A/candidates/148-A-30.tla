---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*********************************************************************
 * Constants (as required by the .cfg file)
 *********************************************************************)

CONSTANTS
    Hash,               \* The universe of possible block hashes
    NoHashVal,          \* Sentinel hash indicating "no previous block"
    PrivateKey,         \* Set of private keys in the system
    PublicKey,          \* Set of public keys in the system
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total coin supply (a natural number)
    NoBlockVal,         \* Sentinel block value meaning "empty slot"
    CalculateHash,      \* Abstract hash calculation operator
    NoHash,             \* Alternative sentinel for hash (kept for cfg compatibility)
    NoBlock             \* Alternative sentinel for block (kept for cfg compatibility)

\* NoHash and NoBlock are defined to be equal to their ...Val counterparts
NoHash == NoHashVal
NoBlock == NoBlockVal

(*********************************************************************
 * Types
 *********************************************************************)

NodeSet == Node
HashSet == Hash

\* Mapping from private to public keys (must be a total function)
KeyMap \* provided as a constant mapping in the .cfg
    \* For safety we assert it is a function from PrivateKey to PublicKey
ASSUME KeyMap \in [PrivateKey -> PublicKey]

\* Account identifier is the public key of the owner
Account == PublicKey

\* Block types
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

\* Block record definition
Block == [
    type          : BlockType,
    hash          : Hash,
    prevHash      : Hash,
    account       : Account,          \* owner of the chain this block belongs to
    data          : STRING,           \* arbitrary payload (e.g., amount, recipient, rep)
    signature     : STRING            \* abstract signature
]

\* Empty sentinel block value
EmptyBlock == NoBlock

\* For convenience, we define the set of all possible blocks (including the sentinel)
AllBlocks == {EmptyBlock} \cup Block

(*********************************************************************
 * State variables
 *********************************************************************)

VARIABLES
    lastHash,          \* The most recent block hash known globally
    ledger,            \* Mapping: Node -> [Hash -> Block] (distributed ledger per node)
    received           \* Mapping: Node -> SUBSET Hash (blocks awaiting processing)

(*********************************************************************
 * Helper definitions
 *********************************************************************)

\* The set of all hashes that may appear (including the sentinel)
AllHashes == Hash \cup {NoHashVal}

\* Helper to extract a block from a node's ledger
BlockAt(node, h) == ledger[node][h]

\* The public key owning a given account (the account is itself a public key)
OwnerOf(account) == account

\* Abstract signature verification: true iff the signature string ends with the owner's public key
SignatureOK(sig, acct) ==
    /\ sig \in STRING
    /\ acct \in Account
    /\ StringSuffix(sig, acct)  \* simple placeholder for real crypto check

\* Balance calculation for an account on a given node
Balance(node, acct) ==
    LET chain == [h \in AllHashes |-> IF BlockAt(node, h).account = acct THEN BlockAt(node, h) ELSE EmptyBlock] IN
    BalanceFromChain(chain, NoHashVal)

BalanceFromChain(chain, startHash) ==
    IF startHash = NoHashVal THEN
        0
    ELSE
        LET blk == chain[startHash] IN
        IF blk = EmptyBlock THEN
            0
        ELSE
            CASE blk.type = "Genesis" -> 0
                 [] blk.type = "Send"   -> BalanceFromChain(chain, blk.prevHash) - ToNat(blk.data)
                 [] blk.type = "Receive"-> BalanceFromChain(chain, blk.prevHash) + ToNat(blk.data)
                 [] OTHER               -> BalanceFromChain(chain, blk.prevHash)

\* Amount extraction (the 'data' field holds the amount as a decimal string)
ToNat(s) == 
    IF s = "" THEN 0 ELSE
    IF \A i \in 1..Len(s) : s[i] \in "0123456789" THEN
        10 ^ (Len(s)-1) * (s[1] - "0") + ToNat(SubSeq(s, 2, Len(s)))
    ELSE 0

\* The set of all send blocks that have not yet been received by a node
UnclaimedSends(node, acct) ==
    { h \in AllHashes :
        LET blk == BlockAt(node, h) IN
        /\ blk.type = "Send"
        /\ blk.account = acct
        /\ ~\E n \in Node : 
                \E hr \in received[n] :
                    BlockAt(n, hr).type = "Receive"
                    /\ BlockAt(n, hr).data = blk.data
                    /\ BlockAt(n, hr).prevHash = blk.hash }

\*********************************************************************
 * Initial state (Init)
 *********************************************************************)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in AllHashes |-> EmptyBlock]]
    /\ received = [n \in Node |-> {}]

(*********************************************************************
 * Actions
 *********************************************************************)

\* Broadcast a block to all nodes' received sets
Broadcast(block) ==
    /\ block.type # "Genesis" => 
        /\ block.prevHash = lastHash
    /\ lastHash' = block.hash
    /\ ledger' = ledger
    /\ received' = [n \in Node |-> received[n] \cup {block.hash}]

\* Genesis block creation (once)
Genesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PrivateKey :
        LET pub == KeyMap[pk] IN
        LET blk == [
            type      |-> "Genesis",
            hash      |-> CalculateHash("Genesis", NoHashVal, pub, "", ""),
            prevHash  |-> NoHashVal,
            account   |-> pub,
            data      |-> ToString(GenesisBalance),   \* amount stored as string
            signature |-> pub \* placeholder signature
        ] IN
        /\ block = blk
        /\ SignatureOK(block.signature, block.account)
        /\ Broadcast(block)
    /\ UNCHANGED << ledger, received >>

\* Send block creation
Send(node, pk, recipient, amount) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ KeyMap[pk] = senderAcct
    /\ senderAcct = OwnerOf(senderAcct)
    /\ amount \in Nat
    /\ Balance(node, senderAcct) >= amount
    /\ LET prevH == lastHash IN
       LET blk == [
            type      |-> "Send",
            hash      |-> CalculateHash("Send", prevH, senderAcct, ToString(amount), recipient),
            prevHash  |-> prevH,
            account   |-> senderAcct,
            data      |-> ToString(amount),
            signature |-> senderAcct \* placeholder
        ] IN
        /\ SignatureOK(blk.signature, blk.account)
        /\ Broadcast(blk)
    /\ UNCHANGED << ledger, received >>

\* Open block creation (for a new account)
Open(node, pk, sendHash) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ KeyMap[pk] = acct
    /\ \E senderNode \in Node :
        LET sb == BlockAt(senderNode, sendHash) IN
        /\ sb.type = "Send"
        /\ sb.data = amountStr
        /\ amountStr \in STRING
        /\ sb.account = senderAcct
        /\ acct = OwnerOf(acct)   \* trivially true, kept for readability
        /\ ~\E h \in AllHashes : 
                BlockAt(node, h).type = "Open"
                /\ BlockAt(node, h).account = acct
        /\ LET blk == [
                type      |-> "Open",
                hash      |-> CalculateHash("Open", NoHashVal, acct, amountStr, senderAcct),
                prevHash  |-> NoHashVal,
                account   |-> acct,
                data      |-> amountStr,
                signature |-> acct
            ] IN
            /\ SignatureOK(blk.signature, blk.account)
            /\ Broadcast(blk)
    /\ UNCHANGED << ledger, received >>

\* Receive block creation
Receive(node, pk, prevHash, sendHash) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ KeyMap[pk] = acct
    /\ prevBlk == BlockAt(node, prevHash)
    /\ prevBlk # EmptyBlock
    /\ sendBlk == 
        CHOOSE n \in Node : BlockAt(n, sendHash).type = "Send"
    /\ sendBlk # EmptyBlock
    /\ sendBlk.account # acct   \* ensure it's not a self-send (simplification)
    /\ LET blk == [
            type      |-> "Receive",
            hash      |-> CalculateHash("Receive", prevHash, acct, sendBlk.data, sendHash),
            prevHash  |-> prevHash,
            account   |-> acct,
            data      |-> sendBlk.data,
            signature |-> acct
        ] IN
        /\ SignatureOK(blk.signature, blk.account)
        /\ Broadcast(blk)
    /\ UNCHANGED << ledger, received >>

\* Change representative block creation
ChangeRep(node, pk, newRep) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ KeyMap[pk] = acct
    /\ prevBlk == BlockAt(node, lastHash)
    /\ prevBlk # EmptyBlock
    /\ LET blk == [
            type      |-> "ChangeRep",
            hash      |-> CalculateHash("ChangeRep", lastHash, acct, newRep, ""),
            prevHash  |-> lastHash,
            account   |-> acct,
            data      |-> newRep,
            signature |-> acct
        ] IN
        /\ SignatureOK(blk.signature, blk.account)
        /\ Broadcast(blk)
    /\ UNCHANGED << ledger, received >>

\* Processing (validation) of a received block by a node
Process(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET blk == BlockAt(node, h) IN
        blk = EmptyBlock => 
            (* block not yet in ledger; fetch from broadcast *)
            LET sourceNode == CHOOSE n \in Node : BlockAt(n, h) # EmptyBlock IN
            LET realBlk == BlockAt(sourceNode, h) IN
            /\ SignatureOK(realBlk.signature, realBlk.account)
            /\ ledger' = [ledger EXCEPT ![node][h] = realBlk]
            /\ received' = [received EXCEPT ![node] = received[node] \ {h}]
            /\ UNCHANGED lastHash
        /\ other => 
            (* block already present; just remove from received *)
            ledger' = ledger
            /\ received' = [received EXCEPT ![node] = received[node] \ {h}]
            /\ UNCHANGED lastHash

\*********************************************************************
 * Next-state relation
 *********************************************************************)

Next ==
    \/ \E node, pk, recipient, amt :
            Send(node, pk, recipient, amt)
    \/ \E node, pk, sendH :
            Open(node, pk, sendH)
    \/ \E node, pk, prevH, sendH :
            Receive(node, pk, prevH, sendH)
    \/ \E node, pk, newRep :
            ChangeRep(node, pk, newRep)
    \/ \E node :
            Process(node)

(*********************************************************************
 * Specification
 *********************************************************************)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(*********************************************************************
 * Invariants
 *********************************************************************)

\* Type invariant (ensures variables stay within their declared domains)
TypeInvariant ==
    /\ lastHash \in AllHashes
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ \A n \in Node : \A h \in AllHashes :
        BlockAt(n, h) \in AllBlocks

\* Safety invariant: every block stored in any ledger has a valid signature
SafetyInvariant ==
    \A n \in Node : \A h \in AllHashes :
        LET blk == BlockAt(n, h) IN
        blk = EmptyBlock \/ SignatureOK(blk.signature, blk.account)

=============================================================================