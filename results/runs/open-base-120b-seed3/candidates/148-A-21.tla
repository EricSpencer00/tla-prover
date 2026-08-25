---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock,
    PrivateToPublic, NodePrivKey, Blocks

VARIABLES
    LastHash, Ledger, Received

(* ---------- Types ---------- *)

HashSet == Hash

Block == [kind       : {"genesis", "send", "receive", "open", "change"},
          prev       : Hash,
          account    : PublicKey,
          recipient  : PublicKey,
          amount     : Nat,
          sig        : PrivateKey,
          referenced : Hash]

NoHash == NoHashVal
NoBlock == NoBlockVal

(* ---------- Helper functions ---------- *)

CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : h # NoHash

ValidSignature(b) ==
    PrivateToPublic[b.sig] = b.account

Balance(account, ledger) ==
    LET chain == {h \in Hash : ledger[h].account = account} IN
    IF chain = {} THEN 0
    ELSE
        Sum({ IF ledger[h].kind = "receive" THEN ledger[h].amount
             ELSIF ledger[h].kind = "send"    THEN -ledger[h].amount
             ELSIF ledger[h].kind = "genesis" THEN ledger[h].amount
             ELSE 0
             END
             : h \in chain})

ValidBlock(node, h) ==
    LET b == Ledger[node][h] IN
    /\ b # NoBlock
    /\ ValidSignature(b)
    /\ IF b.kind = "send" THEN b.amount <= Balance(b.account, Ledger[node]) ELSE TRUE
    /\ IF b.kind = "receive" THEN
          /\ b.referenced # NoHash
          /\ Ledger[node][b.referenced] # NoBlock
          /\ Ledger[node][b.referenced].kind = "send"
          /\ Ledger[node][b.referenced].recipient = b.account
       ELSE TRUE
    /\ IF b.kind = "open" THEN
          /\ b.prev = NoHash
          /\ b.referenced # NoHash
          /\ Ledger[node][b.referenced].kind = "send"
          /\ Ledger[node][b.referenced].recipient = b.account
       ELSE TRUE
    /\ IF b.kind = "change" THEN b.prev # NoHash ELSE TRUE
    /\ IF b.kind = "genesis" THEN
          /\ b.prev = NoHash
          /\ b.amount = GenesisBalance
       ELSE TRUE

(* ---------- Init ---------- *)

Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]

(* ---------- Actions ---------- *)

CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodePrivKey[n]] IN
        LET b  == [kind       |-> "genesis",
                   prev       |-> NoHash,
                   account    |-> pk,
                   recipient  |-> pk,
                   amount     |-> GenesisBalance,
                   sig        |-> NodePrivKey[n],
                   referenced |-> NoHash] IN
        LET h  == CalculateHashImpl(b, LastHash) IN
        /\ h # NoHash
        /\ LastHash' = h
        /\ Ledger'   = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {h}]
    /\ UNCHANGED <<>>

CreateSend ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET pk  == PrivateToPublic[NodePrivKey[n]] IN
        LET bal == Balance(pk, Ledger[n]) IN
        /\ bal > 0
        /\ \E amt \in Nat :
            /\ amt <= bal
            /\ \E rcpt \in PublicKey :
                LET b == [kind       |-> "send",
                          prev       |-> LastHash,
                          account    |-> pk,
                          recipient  |-> rcpt,
                          amount     |-> amt,
                          sig        |-> NodePrivKey[n],
                          referenced |-> NoHash] IN
                LET h == CalculateHashImpl(b, LastHash) IN
                /\ h # NoHash
                /\ LastHash' = h
                /\ Ledger'   = Ledger
                /\ Received' = [m \in Node |-> Received[m] \cup {h}]
    /\ UNCHANGED <<>>

CreateOpen ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodePrivKey[n]] IN
        /\ \E sendHash \in Hash :
            /\ Ledger[n][sendHash].kind = "send"
            /\ Ledger[n][sendHash].recipient = pk
            /\ Ledger[n][sendHash].prev # NoHash
            LET b == [kind       |-> "open",
                      prev       |-> NoHash,
                      account    |-> pk,
                      recipient  |-> pk,
                      amount     |-> Ledger[n][sendHash].amount,
                      sig        |-> NodePrivKey[n],
                      referenced |-> sendHash] IN
            LET h == CalculateHashImpl(b, LastHash) IN
            /\ h # NoHash
            /\ LastHash' = h
            /\ Ledger'   = Ledger
            /\ Received' = [m \in Node |-> Received[m] \cup {h}]
    /\ UNCHANGED <<>>

CreateReceive ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodePrivKey[n]] IN
        /\ \E sendHash \in Hash :
            /\ Ledger[n][sendHash].kind = "send"
            /\ Ledger[n][sendHash].recipient = pk
            /\ Ledger[n][sendHash].prev # NoHash
            LET b == [kind       |-> "receive",
                      prev       |-> LastHash,
                      account    |-> pk,
                      recipient  |-> pk,
                      amount     |-> Ledger[n][sendHash].amount,
                      sig        |-> NodePrivKey[n],
                      referenced |-> sendHash] IN
            LET h == CalculateHashImpl(b, LastHash) IN
            /\ h # NoHash
            /\ LastHash' = h
            /\ Ledger'   = Ledger
            /\ Received' = [m \in Node |-> Received[m] \cup {h}]
    /\ UNCHANGED <<>>

CreateChange ==
    /\ LastHash # NoHash
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodePrivKey[n]] IN
        LET b  == [kind       |-> "change",
                   prev       |-> LastHash,
                   account    |-> pk,
                   recipient  |-> pk,
                   amount     |-> 0,
                   sig        |-> NodePrivKey[n],
                   referenced |-> NoHash] IN
        LET h  == CalculateHashImpl(b, LastHash) IN
        /\ h # NoHash
        /\ LastHash' = h
        /\ Ledger'   = Ledger
        /\ Received' = [m \in Node |-> Received[m] \cup {h}]
    /\ UNCHANGED <<>>

ProcessReceived ==
    /\ \E n \in Node :
        /\ \E h \in Received[n] :
            LET blk == Blocks[h] IN
            /\ blk # NoBlock
            /\ ValidSignature(blk)
            /\ Ledger'   = [Ledger EXCEPT ![n][h] = blk]
            /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
            /\ UNCHANGED LastHash
    /\ UNCHANGED <<>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

(* ---------- Specification ---------- *)

Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

(* ---------- Invariants ---------- *)

TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger   \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == Ledger[n][h] IN
            b # NoBlock => PrivateToPublic[b.sig] = b.account

====