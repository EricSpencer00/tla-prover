---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants (to be bound in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Hash,               \* The set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning “no hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (natural number)
    NoBlockVal,         \* Sentinel value meaning “no block”
    CalculateHash,      \* Abstract hash operator: [data, prevHash] -> Hash
    NoHash,             \* Alias for NoHashVal (for readability)
    NoBlock             \* Alias for NoBlockVal (for readability)

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
PublicKeyOf == { pk \in PublicKey : \E sk \in PrivateKey : PubKeyOf[sk] = pk }

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)
BlockType == {"genesis", "send", "open", "receive", "change"}

VARIABLES
    lastHash,           \* The last calculated block hash (or NoHash)
    ledger,             \* [node -> [hash -> BlockOrNil]]
    recvSets            \* [node -> SUBSET Hash]

(* ----------------------------------------------------------------------
   Block record definition (using a function record)
   ---------------------------------------------------------------------- *)
BlockOrNil == 
    [type       : BlockType,
     hash       : Hash,
     prevHash   : Hash,
     account    : PublicKey,
     targetHash : Hash,
     amount     : Nat,
     representative : PublicKey,
     signer     : PrivateKey] \cup { NoBlock }

(* ----------------------------------------------------------------------
   Helper functions
   ---------------------------------------------------------------------- *)

(* The public key that corresponds to a private key. Must be supplied in .cfg *)
PubKeyOf == [sk \in PrivateKey |-> CHOOSE pk \in PublicKey : pk \in PublicKey]

(* Balance of an account on a given node, computed by walking its chain *)
RecBalance(node, pk) ==
    LET chain == ChainFor(node, pk) IN
    IF chain = <<>> THEN 0
    ELSE BalanceFromChain(chain)

ChainFor(node, pk) ==
    \* Return the sequence of blocks belonging to account pk on node,
    \* ordered from the genesis/open block to the most recent.
    LET allBlocks == { b \in Hash : ledger[node][b] # NoBlock } IN
    LET accBlocks == { b \in allBlocks : ledger[node][b].account = pk } IN
    (* order by the prevHash relation; assume well‑formed *)
    SortByPrev(accBlocks)

SortByPrev(blockSet) ==
    (* Returns a sequence of hashes ordered by the prevHash links.
       For simplicity in the specification we abstract this ordering. *)
    CHOOSE seq \in Seq(blockSet) :
        /\ Len(seq) = Cardinality(blockSet)
        /\ \A i \in 1..Len(seq)-1 : ledger[Node][seq[i+1]].prevHash = seq[i]

BalanceFromChain(seq) ==
    IF seq = <<>> THEN 0
    ELSE
        LET firstHash == seq[1] IN
        LET firstBlock == ledger[Node][firstHash] IN
        IF firstBlock.type = "genesis" THEN GenesisBalance
        ELSE IF firstBlock.type = "open" THEN
            LET sendBlock == ledger[Node][firstBlock.targetHash] IN
            sendBlock.amount
        ELSE (* send, receive, change *)
            BalanceFromChain(<<seq[2..Len(seq)]>>)
            + 
            (CASE seq[Len(seq)].type = "receive" -> seq[Len(seq)].amount
                  [] seq[Len(seq)].type = "send"    -> -seq[Len(seq)].amount
                  [] OTHER                         -> 0)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ recvSets = [n \in Node |-> {}]

(* ----------------------------------------------------------------------
   Block creation actions
   ---------------------------------------------------------------------- *)

CreateGenesis(node) ==
    \E pk \in PublicKey :
    LET sk == CHOOSE k \in PrivateKey : PubKeyOf[k] = pk IN
    LET blk ==
        [type            |-> "genesis",
         hash            |-> CalculateHash([type |-> "genesis", account |-> pk,
                                          amount |-> GenesisBalance,
                                          prevHash |-> NoHash], NoHash),
         prevHash        |-> NoHash,
         account         |-> pk,
         targetHash      |-> NoHash,
         amount          |-> GenesisBalance,
         representative |-> pk,
         signer          |-> sk] IN
    /\ lastHash = NoHash
    /\ ledger' = [n \in Node |-> ledger[n] @@ [blk.hash |-> blk]]
    /\ lastHash' = blk.hash
    /\ recvSets' = recvSets
    /\ UNCHANGED << >>

CreateSend(node, pk, targetPk, amt) ==
    \E prevBlk \in Hash :
    /\ ledger[node][prevBlk] # NoBlock
    /\ ledger[node][prevBlk].account = pk
    /\ ledger[node][prevBlk].type \in {"genesis", "receive", "send", "open", "change"}
    /\ RecBalance(node, pk) >= amt
    /\ LET sk == CHOOSE k \in PrivateKey : PubKeyOf[k] = pk IN
       LET blk ==
        [type            |-> "send",
         hash            |-> CalculateHash([type |-> "send", account |-> pk,
                                          target |-> targetPk, amount |-> amt,
                                          prevHash |-> prevBlk], prevBlk),
         prevHash        |-> prevBlk,
         account         |-> pk,
         targetHash      |-> NoHash,
         amount          |-> amt,
         representative |-> ledger[node][prevBlk].representative,
         signer          |-> sk] IN
    /\ ledger' = [n \in Node |-> ledger[n] @@ [blk.hash |-> blk]]
    /\ lastHash' = blk.hash
    /\ recvSets' = [n \in Node |-> recvSets[n] \cup {blk.hash}]
    /\ UNCHANGED << >>

CreateOpen(node, targetHash, pk) ==
    \E sendBlk \in Hash :
    /\ ledger[node][sendBlk].type = "send"
    /\ ledger[node][sendBlk].targetHash = NoHash
    /\ ledger[node][sendBlk].targetHash = NoHash
    /\ ledger[node][sendBlk].account # pk
    /\ ledger[node][sendBlk].account = PubKeyOf[CHOOSE sk \in PrivateKey :
                                                PubKeyOf[sk] = pk]
    /\ LET blk ==
        [type            |-> "open",
         hash            |-> CalculateHash([type |-> "open", account |-> pk,
                                          targetHash |-> sendBlk],
                                          NoHash),
         prevHash        |-> NoHash,
         account         |-> pk,
         targetHash      |-> sendBlk,
         amount          |-> ledger[node][sendBlk].amount,
         representative |-> ledger[node][sendBlk].representative,
         signer          |-> CHOOSE sk \in PrivateKey : PubKeyOf[sk] = pk] IN
    /\ ledger' = [n \in Node |-> ledger[n] @@ [blk.hash |-> blk]]
    /\ lastHash' = blk.hash
    /\ recvSets' = [n \in Node |-> recvSets[n] \cup {blk.hash}]
    /\ UNCHANGED << >>

CreateReceive(node, pk, sendHash) ==
    \E prevBlk \in Hash :
    /\ ledger[node][prevBlk].account = pk
    /\ ledger[node][prevBlk].type \in {"genesis", "receive", "send", "open", "change"}
    /\ ledger[node][sendHash].type = "send"
    /\ ledger[node][sendHash].account # pk
    /\ ledger[node][sendHash].targetHash = NoHash
    /\ LET blk ==
        [type            |-> "receive",
         hash            |-> CalculateHash([type |-> "receive", account |-> pk,
                                          targetHash |-> sendHash,
                                          prevHash |-> prevBlk],
                                          prevBlk),
         prevHash        |-> prevBlk,
         account         |-> pk,
         targetHash      |-> sendHash,
         amount          |-> ledger[node][sendHash].amount,
         representative |-> ledger[node][prevBlk].representative,
         signer          |-> CHOOSE sk \in PrivateKey : PubKeyOf[sk] = pk] IN
    /\ ledger' = [n \in Node |-> ledger[n] @@ [blk.hash |-> blk]]
    /\ lastHash' = blk.hash
    /\ recvSets' = [n \in Node |-> recvSets[n] \cup {blk.hash}]
    /\ UNCHANGED << >>

CreateChange(node, pk, newRep) ==
    \E prevBlk \in Hash :
    /\ ledger[node][prevBlk].account = pk
    /\ ledger[node][prevBlk].type \in {"genesis", "receive", "send", "open", "change"}
    /\ LET blk ==
        [type            |-> "change",
         hash            |-> CalculateHash([type |-> "change", account |-> pk,
                                          newRep |-> newRep,
                                          prevHash |-> prevBlk],
                                          prevBlk),
         prevHash        |-> prevBlk,
         account         |-> pk,
         targetHash      |-> NoHash,
         amount          |-> 0,
         representative |-> newRep,
         signer          |-> CHOOSE sk \in PrivateKey : PubKeyOf[sk] = pk] IN
    /\ ledger' = [n \in Node |-> ledger[n] @@ [blk.hash |-> blk]]
    /\ lastHash' = blk.hash
    /\ recvSets' = [n \in Node |-> recvSets[n] \cup {blk.hash}]
    /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   Processing of received blocks
   ---------------------------------------------------------------------- *)

ProcessRecv(node) ==
    \E h \in recvSets[node] :
    LET blk == ledger[node][h] IN
    /\ blk # NoBlock
    /\ SignatureValid(blk)
    /\ /\ (blk.type = "send" => 
            /\ ledger[node][blk.prevHash] # NoBlock
            /\ ledger[node][blk.prevHash].account = blk.account
            /\ ledger[node][blk.prevHash].type # "send")
       /\ (blk.type = "receive" => 
            /\ ledger[node][blk.targetHash] # NoBlock
            /\ ledger[node][blk.targetHash].type = "send"
            /\ ledger[node][blk.targetHash].account # blk.account)
       /\ (blk.type = "open" => 
            /\ ledger[node][blk.targetHash] # NoBlock
            /\ ledger[node][blk.targetHash].type = "send"
            /\ ledger[node][blk.targetHash].account # blk.account)
       /\ (blk.type = "change" => TRUE)
       /\ (blk.type = "genesis" => ledger[node] = [h2 \in Hash |-> NoBlock])
    /\ ledger' = ledger
    /\ recvSets' = [n \in Node |-> IF n = node THEN recvSets[n] \ {h} ELSE recvSets[n]]
    /\ UNCHANGED << >>

SignatureValid(blk) ==
    /\ PubKeyOf[blk.signer] = blk.account

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E n \in Node : CreateSend(n, _, _, _)
    \/ \E n \in Node : CreateOpen(n, _, _)
    \/ \E n \in Node : CreateReceive(n, _, _)
    \/ \E n \in Node : CreateChange(n, _, _)
    \/ \E n \in Node : ProcessRecv(n)
    \/ \E n \in Node : CreateGenesis(n)

Spec == Init /\ [][Next]_<<lastHash, ledger, recvSets>>

(* ----------------------------------------------------------------------
   Safety invariant (requires a valid signature for every recorded block)
   ---------------------------------------------------------------------- *)
SafetyInvariant ==
    \A n \in Node : \A h \in Hash :
        ledger[n][h] # NoBlock => SignatureValid(ledger[n][h])

(* ----------------------------------------------------------------------
   Type invariant (as required by the description)
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Node -> [Hash -> (BlockOrNil)]]
    /\ recvSets \in [Node -> SUBSET Hash]

====