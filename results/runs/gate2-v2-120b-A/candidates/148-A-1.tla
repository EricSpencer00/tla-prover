---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ---------- CONSTANTS ---------- *)
CONSTANTS
    Hash,                \* the universe of possible block hashes
    NoHashVal,           \* sentinel value indicating "no hash"
    NoHash,              \* same as NoHashVal, exported for convenience
    PrivateKey,          \* set of all private keys
    PublicKey,           \* set of all public keys
    Node,                \* set of all network nodes
    GenesisBalance,      \* total supply of coins (natural number)
    NoBlockVal,          \* sentinel block value ("empty")
    CalculateHash,       \* abstract hash function: [data -> Hash]
    NoBlock              \* same as NoBlockVal, exported for convenience

NoHash == NoHashVal
NoBlock == NoBlockVal

(* ---------- DERIVED CONSTANTS ---------- *)
(* Mapping from private keys to their public counterpart *)
KeyMap == [pk \in PrivateKey |-> CHOOSE pk2 \in PublicKey : TRUE]

(* ---------- TYPES ---------- *)
VARIABLES
    lastHash,            \* the hash of the most recent block in the system (or NoHash)
    ledger,              \* [n \in Node -> [h \in Hash -> NoBlock \cup Block]]
    received              \* [n \in Node -> SUBSET Hash]  (hashes awaiting validation)

(* ---------- BLOCK RECORD ---------- *)
Block == [
    type            : {"Genesis", "Send", "Open", "Receive", "Change"},
    account         : PublicKey,
    prev            : Hash,
    amount          : Nat,
    recipient       : PublicKey,
    source          : Hash,
    representative  : PublicKey,
    signature       : Seq(Char)
]

\* a convenient predicate to test that a block belongs to a specific account chain
IsInChain(b, acc) == b.account = acc

(* ---------- INITIAL STATE ---------- *)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(* ---------- HELPER FUNCTIONS ---------- *)

(* returns the public key owning a given account chain (the account itself) *)
AccountOwner(b) == b.account

(* checks a signature – abstract, always true for the model *)
ValidSignature(b) == TRUE

(* looks up the block with a given hash in a node's ledger *)
Lookup(n, h) == ledger[n][h]

(* computes the balance of an account on a given node by walking its chain *)
BalanceOf(n, acc) ==
    LET
        chain == { b \in { b : \E h \in Hash : ledger[n][h] = b } :
                    b.account = acc }
        latest == { b \in chain : 
                     \A b2 \in chain : b2.prev # b.hash => b2.hash # b.prev }
        Rec(b) == IF b.type = "Genesis" THEN b.amount
                  ELSE IF b.type = "Send" THEN 0
                  ELSE IF b.type = "Open" THEN b.amount
                  ELSE IF b.type = "Receive" THEN b.amount + Rec(Lookup(n, b.source))
                  ELSE IF b.type = "Change" THEN Rec(Lookup(n, b.prev))
                  ELSE 0
    IN IF latest = {} THEN 0 ELSE Rec(CHOOSE b \in latest : TRUE)

(* ---------- ACTIONS ---------- *)

(* Genesis block creation – can only happen once, when no other block exists *)
GenesisCreate ==
    /\ lastHash = NoHash
    /\ \E pk \in PrivateKey :
        LET
            pub == KeyMap[pk]
            gblk == [
                type            |-> "Genesis",
                account         |-> pub,
                prev            |-> NoHash,
                amount          |-> GenesisBalance,
                recipient       |-> pub,
                source          |-> NoHash,
                representative |-> pub,
                signature       |-> "sig",      \* abstract
                hash            |-> CalculateHash(<< "Genesis", pub, GenesisBalance >>)
            ]
        IN
            /\ lastHash' = gblk.hash
            /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![gblk.hash] = gblk]]
            /\ received' = [n \in Node |-> {}]
            /\ UNCHANGED << >>

(* Create a Send block *)
SendCreate ==
    /\ \E n \in Node :
        \E pk \in PrivateKey :
            LET
                pub == KeyMap[pk]
                \* find the latest block of the sender
                chain == { b \in { b : \E h \in Hash : ledger[n][h] = b } :
                            b.account = pub }
                latest == { b \in chain : 
                             \A b2 \in chain : b2.prev # b.hash => b2.hash # b.prev }
                prevBlk == CHOOSE b \in latest : TRUE
                bal == BalanceOf(n, pub)
                amt \in 0..bal
                sbHash == CalculateHash(<< "Send", pub, prevBlk.hash, amt, NoHash >>)
                sblk == [
                    type            |-> "Send",
                    account         |-> pub,
                    prev            |-> prevBlk.hash,
                    amount          |-> amt,
                    recipient       |-> NoHash,
                    source          |-> NoHash,
                    representative |-> NoHash,
                    signature       |-> "sig",
                    hash            |-> sbHash
                ]
            IN
                /\ lastHash' = sbHash
                /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![sbHash] = sblk]]
                /\ received' = [n2 \in Node |-> received[n2] \cup {sbHash}]
                /\ UNCHANGED << >>

(* Open a new account *)
OpenCreate ==
    /\ \E n \in Node :
        \E sendHash \in Hash :
            LET
                sendBlk == ledger[n][sendHash]
            IN
                /\ sendBlk.type = "Send"
                /\ sendBlk.recipient = NoHash
                /\ \E pk \in PrivateKey :
                    LET
                        pub == KeyMap[pk]
                        openHash == CalculateHash(<< "Open", pub, sendHash, sendBlk.amount >>)
                        oblck == [
                            type            |-> "Open",
                            account         |-> pub,
                            prev            |-> NoHash,
                            amount          |-> sendBlk.amount,
                            recipient       |-> NoHash,
                            source          |-> sendHash,
                            representative |-> pub,
                            signature       |-> "sig",
                            hash            |-> openHash
                        ]
                    IN
                        /\ lastHash' = openHash
                        /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![openHash] = oblck]]
                        /\ received' = [n2 \in Node |-> received[n2] \cup {openHash}]
                        /\ UNCHANGED << >>

(* Receive a pending send *)
ReceiveCreate ==
    /\ \E n \in Node :
        \E recvHash \in Hash :
            LET
                recvBlk == ledger[n][recvHash]
            IN
                /\ recvBlk.type = "Receive"
                /\ \E sendHash \in Hash :
                    LET
                        sendBlk == ledger[n][sendHash]
                    IN
                        /\ sendBlk.type = "Send"
                        /\ sendBlk.recipient = recvBlk.account
                        /\ recvBlk.source = sendHash
                        /\ recvBlk.prev = recvHash
                        /\ lastHash' = recvBlk.hash
                        /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![recvBlk.hash] = recvBlk]]
                        /\ received' = [n2 \in Node |-> received[n2] \cup {recvBlk.hash}]
                        /\ UNCHANGED << >>

(* Change representative *)
ChangeRepCreate ==
    /\ \E n \in Node :
        \E pk \in PrivateKey :
            LET
                pub == KeyMap[pk]
                chain == { b \in { b : \E h \in Hash : ledger[n][h] = b } :
                            b.account = pub }
                latest == { b \in chain : 
                             \A b2 \in chain : b2.prev # b.hash => b2.hash # b.prev }
                prevBlk == CHOOSE b \in latest : TRUE
                newRep \in PublicKey
                chHash == CalculateHash(<< "Change", pub, prevBlk.hash, newRep >>)
                chblk == [
                    type            |-> "Change",
                    account         |-> pub,
                    prev            |-> prevBlk.hash,
                    amount          |-> 0,
                    recipient       |-> NoHash,
                    source          |-> NoHash,
                    representative |-> newRep,
                    signature       |-> "sig",
                    hash            |-> chHash
                ]
            IN
                /\ lastHash' = chHash
                /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![chHash] = chblk]]
                /\ received' = [n2 \in Node |-> received[n2] \cup {chHash}]
                /\ UNCHANGED << >>

(* Processing a received block on a node *)
Process ==
    /\ \E n \in Node :
        \E h \in received[n] :
            LET
                blk == ledger[n][h]
            IN
                /\ ValidSignature(blk)
                /\ (blk.type = "Genesis" => blk.prev = NoHash)
                /\ (blk.type = "Send" => 
                        blk.prev # NoHash /\ 
                        blk.amount <= BalanceOf(n, blk.account))
                /\ (blk.type = "Open" => 
                        blk.prev = NoHash /\ 
                        blk.source # NoHash /\ 
                        ledger[n][blk.source].type = "Send" /\
                        ledger[n][blk.source].recipient = blk.account)
                /\ (blk.type = "Receive" => 
                        blk.prev # NoHash /\ 
                        blk.source # NoHash /\ 
                        ledger[n][blk.source].type = "Send" /\ 
                        ledger[n][blk.source].recipient = blk.account)
                /\ (blk.type = "Change" => blk.prev # NoHash)
                /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \ {h} ELSE received[n2]]
                /\ UNCHANGED << lastHash, ledger >>

(* ---------- NEXT STATE ---------- *)
Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeRepCreate
    \/ Process

(* ---------- SPECIFICATION ---------- *)
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* ---------- INVARIANTS ---------- *)

\* TypeInvariant: ensures that variables stay within their declared types
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (NoBlock \cup Block)]]
    /\ received \in [Node -> SUBSET Hash]

\* SafetyInvariant: every block stored in any ledger has a valid signature
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
                (b = NoBlock) \/ ValidSignature(b)

=============================================================================