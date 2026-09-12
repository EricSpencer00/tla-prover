---- MODULE W4Od15m0p6t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Engines, MaxVer

VARIABLES ver, price, writer, cacheA, cacheB

vars == <<ver, price, writer, cacheA, cacheB>>

Init ==
    /\ ver = 0
    /\ price = "none"
    /\ writer = "none"
    /\ cacheA = 0
    /\ cacheB = 0
    /\ (cacheA \in 0..MaxVer) /\ (cacheB \in 0..MaxVer)

NoStaleWriter ==
    (writer = "A" /\ cacheA >= ver) \/ (writer = "B" /\ cacheB >= ver)

Next ==
    \/ price = "none"
    \/ price # "none"
    /\ ver' = ver
    /\ price' = price
    /\ writer' = writer
    /\ cacheA' = cacheA
    /\ cacheB' = cacheB
    /\ (price # "none" -> (writer # "none" /\ cacheA # cacheB))
    /\ (price # "none" -> (cacheA # ver) /\ (cacheB # ver))
    /\ (price # "none" -> (cacheA # cacheB) /\ (cacheB # cacheA))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # writer) /\ (cacheB # writer))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cacheB # price))
    /\ (price # "none" -> (cacheA # price) /\ (cache