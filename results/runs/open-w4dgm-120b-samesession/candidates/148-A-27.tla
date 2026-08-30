---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

Operators == {NoHashVal} \cup Hash

VARIABLES lastHash, ledger, received

Vars == <<lastHash, ledger, received>>

EmptyLedger == [h \in Operators |-> NoBlockVal]
EmptyReceived == [n \in Node |-> {}]

BlockTypes == {"genesis", "send", "open", "receive", "change"}

RECURSIVE SumR(_)
SumR(S) == IF S = {} THEN 0
           ELSE LET x == CHOOSE y \in S : TRUE IN x + SumR(S \ {x})

RECURSIVE Balance(_)
Balance(s) == IF s = <<>> THEN 0
              ELSE LET blk == Head(s) IN
                    (IF blk.type = "send" THEN -blk.amount ELSE IF blk.type = "receive" THEN blk.amount ELSE 0)
                     + Balance(Tail(s))

RECURSIVE ChainSet(_)
ChainSet(S) == IF S = {} THEN {}
               ELSE LET blk == CHOOSE y \in S : TRUE IN {blk} \cup ChainSet(S \ {blk})

RECURSIVE Chain(_)
Chain(chain) == IF chain = <<>> THEN {}
                ELSE {Head(chain)} \cup Chain(Tail(chain))

RECURSIVE ChainToMap(_)
ChainToMap(chain) ==
    IF chain = <<>> THEN [:]
    ELSE LET blk == Head(chain) IN [blk.hash |-> ChainToMap(Tail(chain))]

RECURSIVE LookupChain(_)
LookupChain(m, h) == IF m = [:] THEN <<>>
                     ELSE IF h \in DOMAIN m THEN
                       LET blk == m[h] IN <<blk>> \o LookupChain(m, blk.prevHash)
                     ELSE IF m = ChainToMap(LookupChain(m, NoHash)) THEN <<>>
                        ELSE LookupChain(ChainToMap(LookupChain(m, NoHash)), h)

RECURSIVE LocateBlock(_)
LocateBlock(m, h) ==
    IF m = [:] THEN NoBlock
    ELSE IF h \in DOMAIN m THEN m[h]
    ELSE LocateBlock(ChainToMap(LookupChain(m, NoHash)), h)

RECURSIVE AmountSentTo(_)
AmountSentTo(n, s) == IF s = <<>> THEN 0
                      ELSE LET blk == Head(s) IN
                            (IF blk.type = "send" /\ blk.recipient = n THEN blk.amount ELSE 0)
                             + AmountSentTo(n, Tail(s))

RECURSIVE AmountReceivedFrom(_)
AmountReceivedFrom(n, s) == IF s = <<>> THEN 0
                            ELSE LET blk == Head(s) IN
                                  (IF blk.type = "receive" /\ blk.sender = n THEN blk.amount ELSE 0)
                                   + AmountReceivedFrom(n, Tail(s))

RECURSIVE ClaimableSet(_)
ClaimableSet(n, s) ==
    IF s = <<>> THEN {}
    ELSE LET blk == Head(s) IN
         IF blk.type = "send" /\ blk.recipient = n /\ AmountSentTo(n, s) > AmountReceivedFrom(n, s)
            THEN {blk} \cup ClaimableSet(n, Tail(s))
            ELSE ClaimableSet(n, Tail(s))

RECURSIVE AccountBalance(_)
AccountBalance(n) == Balance(LookupChain(ChainToMap(LookupChain(ledger[CHOOSE m \in Node : TRUE], NoHash)), n))

TypeInvariant ==
    /\ lastHash \in Operators
    /\ ledger \in [Node -> [Operators -> {"empty", NoBlockVal} \cup [hash: Operators, prevHash: Operators, signer: PrivateKey, type: BlockTypes, recipient: PublicKey, amount: 0..GenesisBalance, sender: PublicKey]]]
    /\ received \in [Node -> SUBSET Operators]

\* Every block in every node's ledger has a genuine signature from the
\* public key of the account that owns the chain it is attached to.
SafetyInvariant ==
    \A n \in Node : \A h \in Operators : ledger[n][h] # "empty" =>
        /\ ledger[n][h].signer \in {k \in PrivateKey : PublicKey[k] = ledger[n][h].signer}
        /\ ledger[n][h].type \in BlockTypes

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> EmptyLedger]
    /\ received = EmptyReceived

CreateGenesisBlock(k) ==
    /\ lastHash = NoHashVal
    /\ lastHash' = CalculateHash(<<"genesis", NoHash, k, GenesisBalance>>, NoHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [hash |-> lastHash, prevHash |-> NoHash, signer |-> k, type |-> "genesis", recipient |-> PublicKey[k], amount |-> GenesisBalance, sender |-> PublicKey[k]]]]
    /\ UNCHANGED received

CreateSendBlock(n, k, rec, amt) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash].type = "genesis" \/ ledger[n][lastHash].type = "receive" \/ ledger[n][lastHash].type = "open"
    /\ amt \in 1..GenesisBalance
    /\ AccountBalance(n) >= amt
    /\ lastHash' = CalculateHash(<<"send", lastHash, k, amt>>, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [hash |-> lastHash, prevHash |-> lastHash, signer |-> k, type |-> "send", recipient |-> rec, amount |-> amt, sender |-> PublicKey[k]]]
    /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateOpenBlock(n, k, h) ==
    /\ LocateBlock(ledger[n], h) # NoBlock
    /\ LocateBlock(ledger[n], h).type = "send"
    /\ LocateBlock(ledger[n], h).recipient = PublicKey[k]
    /\ lastHash' = CalculateHash(<<"open", NoHash, k, LocateBlock(ledger[n], h).amount>>, NoHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [hash |-> lastHash, prevHash |-> NoHash, signer |-> k, type |-> "open", recipient |-> PublicKey[k], amount |-> LocateBlock(ledger[n], h).amount, sender |-> PublicKey[k]]]
    /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateReceiveBlock(n, k, h) ==
    /\ LocateBlock(ledger[n], h) # NoBlock
    /\ LocateBlock(ledger[n], h).type = "send"
    /\ LocateBlock(ledger[n], h).recipient = PublicKey[k]
    /\ lastHash' = CalculateHash(<<"receive", lastHash, k, LocateBlock(ledger[n], h).amount>>, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [hash |-> lastHash, prevHash |-> lastHash, signer |-> k, type |-> "receive", recipient |-> PublicKey[k], amount |-> LocateBlock(ledger[n], h).amount, sender |-> PublicKey[k]]]
    /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateChangeBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash(<<"change", lastHash, k, 0>>, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [hash |-> lastHash, prevHash |-> lastHash, signer |-> k, type |-> "change", recipient |-> PublicKey[k], amount |-> 0, sender |-> PublicKey[k]]]
    /\ UNCHANGED received

ValidateReceived(n, h) ==
    /\ h \in received[n]
    /\ LocateBlock(ledger[n], h) = NoBlock
    /\ LocateBlock(ledger[CHOOSE m \in Node : TRUE], h) # NoBlock
    /\ LocateBlock(ledger[n], LocateBlock(ledger[CHOOSE m \in Node : TRUE], h).prevHash) # NoBlock
    /\ LocateBlock(ledger[n], h).signer = LocateBlock(ledger[n], h).signer
    /\ IF LocateBlock(ledger[n], h).type = "send" THEN LocateBlock(ledger[n], h).amount <= AccountBalance(CCC) ELSE TRUE
    /\ ledger' = [ledger EXCEPT ![n][h] = LocateBlock(ledger[CHOOSE m \in Node : TRUE], h)]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED lastHash

FinishProcessing(n) ==
    /\ \E h \in received[n] : ValidateReceived(n, h)
    /\ UNCHANGED <<lastHash, ledger, received>>

Next ==
    \/ \E n \in Node : FinishProcessing(n)
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ \E n \in Node, k \in PrivateKey, rec \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, rec, amt)
    \/ \E n \in Node, k \in PrivateKey, h \in Operators : CreateOpenBlock(n, k, h)
    \/ \E n \in Node, k \in PrivateKey, h \in Operators : CreateReceiveBlock(n, k, h)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeBlock(n, k)

Spec == Init /\ [][Next]_Vars

AccountBalance(n) == Balance(LookupChain(ChainToMap(LookupChain(ledger[n], NoHash)), n))

BalanceInvariant ==
    SumR({AccountBalance(n) : n \in Node}) <= GenesisBalance

====