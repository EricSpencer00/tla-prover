---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Order of the chain is encoded in each block's hash: a block's hash is the
\* next value in a sequence as it is calculated from the previous one.  Vali-
\* dating itself is order-sensitive, since a receive block must be added after
\* the send block it spends is already in the local ledger.
Blocks == {NoBlock} \cup [hash : Hash, parent : Hash \cup {NoHash}, account : PublicKey,
                          kind : {"genesis", "send", "open", "receive", "change"},
                          amount : Nat, to : PublicKey]

RECURSIVE SumBalances(_)
SumBalances(S) == IF S = {} THEN 0
                  ELSE LET a == CHOOSE e \in S : TRUE IN Balance(a) + SumBalances(S \ {a})

VARIABLES lastHash, dledger, received
vars == << lastHash, dledger, received >>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ dledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Blocks]

Init ==
    /\ lastHash = NoHash
    /\ dledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

AccountBalance(n) == Balance(PublicKeyOf(n))

Balance(p) ==
    LET Chain(S) ==
        IF S = {} THEN {}
        ELSE LET b == CHOOSE e \in S : e.account = p /\ (e.parent = NoHash \/ e.parent \in Chain(S))
             IN {b} \cup Chain(S)
    IN RECURSIVE SumChain(_)
    SumChain(S) == IF S = {} THEN 0
                   ELSE LET b == CHOOSE e \in S : TRUE
                        IN (IF b.kind = "send" THEN -b.amount ELSE IF b.kind = "receive" THEN b.amount ELSE 0)
                            + SumChain(S \ {b})
    IN SumChain(Chain({h \in Hash : dledger[CHOOSE n \in Node : TRUE][h] # NoBlockVal}))

PublicKeyOf(n) == (CHOOSE pk \in PublicKey : \E sk \in PrivateKey : OwnerOf(sk) = n /\ pk = PublicKeyOf(sk))

\* See the comment at the top of the module: CalculateHash is an uninterpreted
\* symbol, so the model is parameterized by CalculateHashImpl.
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E sk \in PrivateKey :
         LET pk == PublicKeyOf(sk) IN
         /\ \A n \in Node : dledger' = [dledger EXCEPT ![n] =
              [h \in Hash |-> IF h = NoHash THEN [hash |-> NoHash, parent |-> NoHash, account |-> pk,
                                                   kind |-> "genesis", amount |-> GenesisBalance,
                                                   to |-> pk]
                             ELSE NoBlockVal]]
    /\ lastHash' = NoHashVal
    /\ received' = [n \in Node |-> {}]

CreateSend(n) ==
    /\ AccountBalance(n) > 0
    /\ \E rec \in PublicKey, amt \in Nat :
         /\ amt <= AccountBalance(n)
         /\ ~ \E b \in {dledger[n][h] : h \in Hash} : b.kind = "send" /\ b.parent = lastHash /\ b.account = PublicKeyOf(n)
         /\ LET h == CalculateHash([parent |-> lastHash, account |-> PublicKeyOf(n), kind |-> "send", amount |-> amt, to |-> rec])
            IN /\ lastHash' = h
               /\ dledger' = [dledger EXCEPT ![n][h] = [hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n),
                                                         kind |-> "send", amount |-> amt, to |-> rec]]
               /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup
                               {[hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n), kind |-> "send", amount |-> amt, to |-> rec]}]

CreateOpen(n) ==
    /\ \E b \in {dledger[m][h] : m \in Node, h \in Hash} :
         /\ b.kind = "send" /\ b.to = PublicKeyOf(n)
         /\ \A e \in {dledger[n][h] : h \in Hash} : e.parent # b.hash
         /\ LET h == CalculateHash([parent |-> NoHash, account |-> PublicKeyOf(n), kind |-> "open", amount |-> 0, to |-> b.hash])
            IN /\ lastHash' = h
               /\ dledger' = [dledger EXCEPT ![n][h] = [hash |-> h, parent |-> NoHash, account |-> PublicKeyOf(n),
                                                         kind |-> "open", amount |-> 0, to |-> b.hash]]
               /\ received' = [m \in Node |-> IF m = n THEN received[m]
                                 ELSE received[m] \cup {[hash |-> h, parent |-> NoHash, account |-> PublicKeyOf(n),
                                                          kind |-> "open", amount |-> 0, to |-> b.hash]}]

CreateReceive(n) ==
    /\ \E b \in {dledger[m][h] : m \in Node, h \in Hash} :
         /\ b.kind = "send" /\ b.to = PublicKeyOf(n)
         /\ \A e \in {dledger[n][h] : h \in Hash} : e.parent # b.hash
         /\ LET h == CalculateHash([parent |-> lastHash, account |-> PublicKeyOf(n), kind |-> "receive", amount |-> b.amount, to |-> b.hash])
            IN /\ lastHash' = h
               /\ dledger' = [dledger EXCEPT ![n][h] = [hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n),
                                                         kind |-> "receive", amount |-> b.amount, to |-> b.hash]]
               /\ received' = [m \in Node |-> IF m = n THEN received[m]
                                 ELSE received[m] \cup {[hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n),
                                                          kind |-> "receive", amount |-> b.amount, to |-> b.hash]}]

CreateChangeRepresentative(n) ==
    /\ ~ \E e \in {dledger[n][h] : h \in Hash} : e.kind = "change"
    /\ LET h == CalculateHash([parent |-> lastHash, account |-> PublicKeyOf(n), kind |-> "change", amount |-> 0, to |-> NoHash])
       IN /\ lastHash' = h
          /\ dledger' = [dledger EXCEPT ![n][h] = [hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n),
                                                    kind |-> "change", amount |-> 0, to |-> NoHash]]
          /\ received' = [m \in Node |-> IF m = n THEN received[m]
                            ELSE received[m] \cup {[hash |-> h, parent |-> lastHash, account |-> PublicKeyOf(n),
                                                     kind |-> "change", amount |-> 0, to |-> NoHash]}]

Validate(n, b) ==
    /\ b \notin received[n]
    /\ dledger[n][b.hash] = NoBlockVal
    /\ VerifySignature(b)
    /\ dledger' = [dledger EXCEPT ![n][b.hash] = b]
    /\ UNCHANGED <<lastHash, received>>

Discard(n, b) ==
    /\ b \in received[n]
    /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED <<lastHash, dledger>>

\* Signature verification is the only place checking the public-key identity
\* of who created a block; it is required for every block type here.
VerifySignature(b) ==
    /\ OwnerOf(PublicKeyOf(b.account)) = b.account
    /\ \/ b.kind = "genesis"
       \/ \E sk \in PrivateKey : OwnerOf(sk) = b.account /\ b.kind \in {"send", "open", "receive"}
       \/ b.kind = "change"
    /\ \/ b.kind \in {"genesis", "open", "change"}
       \/ \E parent \in Hash \cup {NoHash} : b.parent = parent
          /\ dledger[CHOOSE n \in Node : TRUE][parent] # NoBlockVal
    /\ \/ b.kind \in {"open", "receive", "change"}
       \/ \E c \in Hash \cup {NoHash} : b.to = c
          /\ (c = NoHash \/ dledger[CHOOSE n \in Node : TRUE][c] # NoBlockVal)
    /\ \/ b.kind = "send"
       \/ AccountBalance(OwnerOf(PublicKeyOf(b.account))) >= b.amount
    /\ \/ b.kind \in {"receive", "open"}
       \/ \A n \in Node : \A h \in Hash : dledger[n][h] # NoBlockVal => dledger[n][h].hash # b.to

Next ==
    \/ CreateGenesis \/ CreateChangeRepresentative(CHOOSE n \in Node : TRUE)
    \/ \E n \in Node : CreateSend(n) \/ CreateOpen(n) \/ CreateReceive(n)
    \/ \E n \in Node : \E b \in Blocks : Validate(n, b) \/ Discard(n, b)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node : \A h \in Hash : dledger[n][h] # NoBlockVal => VerifySignature(dledger[n][h])

\* The sum of all account balances never exceeds the genesis total.
BalanceConserved == SumBalances(Node) <= GenesisBalance

====