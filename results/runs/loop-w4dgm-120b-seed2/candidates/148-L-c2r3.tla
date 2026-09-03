-------------------------- MODULE Nano --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal,
    CalculateHash,
    NoHash,
    NoBlock

PublicKeyOf == (pk \in PrivateKey) \mapsto PublicKey[pk]

Lattice == [prev : Hash \cup {NoHash}, pub : PublicKey, typ : {"genesis",
    "send", "open", "receive", "changeRep"}, amt : Nat, signer : PrivateKey]

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE
                 IN x.amt + SumOf(S \ {x})

RECURSIVE ChainBalance(_)
ChainBalance(chain) ==
    IF chain = {} THEN 0
    ELSE LET b == CHOOSE y \in chain : TRUE
         IN IF b.typ = "send" THEN ChainBalance(chain \ {b}) - b.amt
            ELSE IF b.typ = "receive" THEN ChainBalance(chain \ {b}) + b.amt
            ELSE ChainBalance(chain \ {b})

RECURSIVE ChainOf(_)
ChainOf(h) ==
    IF h = NoHashVal THEN {}
    ELSE LET b == ChainOf[h]
         IN IF b = NoBlockVal
            THEN {}
            ELSE {b} \cup ChainOf(b.prev)

RECURSIVE AccountChains(_)
AccountChains(S) ==
    IF S = {} THEN {}
    ELSE LET h == CHOOSE y \in S : TRUE
         IN {ChainOf(h)} \cup AccountChains(S \ {h})

RECURSIVE IsSendBlockToNode(_)
IsSendBlockToNode(n) == (n \in PrivateKey) /\ (PublicKeyOf[n] \in PublicKey)

RECURSIVE SendAmountToNode(_)
SendAmountToNode(n) ==
    IF ~IsSendBlockToNode(n) THEN 0
    ELSE ChainBalance(ChainOf(ChainOf[PublicKeyOf[n]]))

RECURSIVE SumOfAccountChains(_)
SumOfAccountChains(S) ==
    IF S = {} THEN 0
    ELSE LET ch == CHOOSE y \in S : TRUE
         IN SumOf(ch) + SumOfAccountChains(S \ {ch})

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Init ==
    /\ lastHash = NoHashVal
    /\ (\A nd \in Node : ledger[nd] = [h \in Hash |-> NoBlockVal] /\ received[nd] = {})
    /\ UNCHANGED <<>>

BroadcastBlock(b) ==
    /\ \A nd \in Node : received' = [received EXCEPT ![nd] = @ \cup {b}]
    /\ UNCHANGED <<lastHash, ledger>>

CreateGenesisBlock ==
    /\ lastHash = NoHashVal
    /\ \E n \in PrivateKey :
        /\ b \in Lattice
        /\ b.typ = "genesis"
        /\ b.pub = PublicKeyOf[n]
        /\ b.amt = GenesisBalance
        /\ b.prev = NoHash
        /\ b.signer = n
        /\ lastHash' = CalculateHash(b, NoHash)
        /\ ledger' = [nd \in Node |-> [ledger[nd] EXCEPT ![lastHash'] = b]]
    /\ \A nd \in Node : received' = received[nd]

CreateSendBlock ==
    /\ \E n \in PrivateKey, a \in Nat, h \in Hash :
        /\ b \in Lattice
        /\ b.typ = "send"
        /\ b.pub = PublicKeyOf[n]
        /\ b.amt = a
        /\ b.prev = h
        /\ b.signer = n
        /\ ChainBalance(ChainOf(h)) >= a
        /\ lastHash' = CalculateHash(b, h)
        /\ ledger' = [nd \in Node |-> [ledger[nd] EXCEPT ![lastHash'] = b]]
    /\ BroadcastBlock(b)

CreateOpenBlock ==
    /\ \E n \in PrivateKey, h \in Hash :
        /\ b \in Lattice
        /\ b.typ = "open"
        /\ b.pub = PublicKeyOf[n]
        /\ b.amt = 0
        /\ b.prev = NoHash
        /\ b.signer = n
        /\ ~IsSendBlockToNode(n)
        /\ lastHash' = CalculateHash(b, h)
        /\ ledger' = [nd \in Node |-> [ledger[nd] EXCEPT ![lastHash'] = b]]
    /\ BroadcastBlock(b)

CreateReceiveBlock ==
    /\ \E n \in PrivateKey, h1 \in Hash, h2 \in Hash :
        /\ b \in Lattice
        /\ b.typ = "receive"
        /\ b.pub = PublicKeyOf[n]
        /\ b.amt = 0
        /\ b.prev = h1
        /\ b.signer = n
        /\ ChainOf(h2) = ChainOf[PublicKeyOf[n]]
        /\ ChainBalance(ChainOf(h2)) = 0
        /\ lastHash' = CalculateHash(b, h1)
        /\ ledger' = [nd \in Node |-> [ledger[nd] EXCEPT ![lastHash'] = b]]
    /\ BroadcastBlock(b)

CreateChangeRepBlock ==
    /\ \E n \in PrivateKey, h \in Hash :
        /\ b \in Lattice
        /\ b.typ = "changeRep"
        /\ b.pub = PublicKeyOf[n]
        /\ b.amt = 0
        /\ b.prev = h
        /\ b.signer = n
        /\ lastHash' = CalculateHash(b, h)
        /\ ledger' = [nd \in Node |-> [ledger[nd] EXCEPT ![lastHash'] = b]]
    /\ BroadcastBlock(b)

ValidateBlock(n, b) ==
    /\ b \in received[n]
    /\ b.signer \in PrivateKey
    /\ PublicKeyOf[b.signer] = b.pub
    /\ ledger[n][b.prev] # NoBlockVal
    /\ IF b.typ = "send" THEN ChainBalance(ChainOf(b.prev)) >= b.amt
       ELSE IF b.typ = "open" THEN ~IsSendBlockToNode(b.signer)
       ELSE IF b.typ = "receive" THEN ChainOf(b.prev) = ChainOf[b.pub]
            /\ ChainBalance(ChainOf(b.prev)) = 0
       ELSE TRUE
    /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![CalculateHash(b, b.prev)] = b]]
    /\ received' = [received EXCEPT ![n] = @ \ {b}]
    /\ UNCHANGED lastHash

ValidateAnyNode == \E n \in Node, b \in received[n] : ValidateBlock(n, b)

Next ==
    \/ CreateGenesisBlock
    \/ CreateSendBlock
    \/ CreateOpenBlock
    \/ CreateReceiveBlock
    \/ CreateChangeRepBlock
    \/ ValidateAnyNode

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ValidateAnyNode)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> Lattice \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Lattice]

SafetyInvariant ==
    \A nd \in Node : \A h \in Hash :
        (ledger[nd][h] # NoBlockVal) => (PublicKeyOf[ledger[nd][h].signer] = ledger[nd][h].pub)

BalanceInvariant == SumOfAccountChains(AccountChains(Hash)) <= GenesisBalance

===============================================================