---- MODULE W4Od10m0p4t2 ----
EXTENDS Integers, FiniteSets

CONSTANTS Capacity, Section, Center1, Center2

VARIABLES occupancy, liveVersion, center1Snapshot, center2Snapshot

TypeOK ==
    occupancy \in 0..Capacity
    liveVersion \in 0..Capacity
    center1Snapshot \in 0..Capacity
    center2Snapshot \in 0..Capacity

Init ==
    /\ occupancy = 0
    /\ liveVersion = 0
    /\ center1Snapshot = 0
    /\ center2Snapshot = 0

Next ==
    /\ liveVersion' = liveVersion
    /\ (IF Section = Center1
        THEN
            /\ occupancy' = (IF Section = Center1
                THEN occupancy + (IF liveVersion = center1Snapshot
                    THEN 1
                    ELSE 0)
                ELSE occupancy)
            /\ (IF Section = Center2
                THEN
                    /\ center2Snapshot' = liveVersion
                    /\ (IF liveVersion = center2Snapshot
                        THEN
                            /\ center2Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        ELSE
                            /\ center2Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        )
                    ELSE
                        /\ center2Snapshot' = liveVersion
                        /\ (IF liveVersion = center2Snapshot
                            THEN
                                /\ center2Snapshot = liveVersion
                                /\ occupancy' = occupancy
                            ELSE
                                /\ center2Snapshot = liveVersion
                                /\ occupancy' = occupancy
                            )
                        )
                ELSE
                    /\ center2Snapshot' = liveVersion
                    /\ (IF liveVersion = center2Snapshot
                        THEN
                            /\ center2Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        ELSE
                            /\ center2Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        )
                    )
        ELSE
            /\ occupancy' = (IF Section = Center2
                THEN occupancy + (IF liveVersion = center2Snapshot
                    THEN 1
                    ELSE 0)
                ELSE occupancy)
            /\ (IF Section = Center1
                THEN
                    /\ center1Snapshot' = liveVersion
                    /\ (IF liveVersion = center1Snapshot
                        THEN
                            /\ center1Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        ELSE
                            /\ center1Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        )
                    ELSE
                        /\ center1Snapshot' = liveVersion
                        /\ (IF liveVersion = center1Snapshot
                            THEN
                                /\ center1Snapshot = liveVersion
                                /\ occupancy' = occupancy
                            ELSE
                                /\ center1Snapshot = liveVersion
                                /\ occupancy' = occupancy
                            )
                        )
                ELSE
                    /\ center1Snapshot' = liveVersion
                    /\ (IF liveVersion = center1Snapshot
                        THEN
                            /\ center1Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        ELSE
                            /\ center1Snapshot = liveVersion
                            /\ occupancy' = occupancy
                        )
                    )
        )
    /\ (IF Section = Center1
        THEN
            /\ liveVersion' = liveVersion + 1
        ELSE
            /\ liveVersion' = liveVersion + 1
        )
    /\ (IF Section = Center1
        THEN
            /\ (IF liveVersion = center1Snapshot
                THEN
                    /\ center1Snapshot = liveVersion
                    /\ Section = Center1
                ELSE
                    /\ Section #<1
                )
            ELSE
                /\ Section #<1
            )
        ELSE
            /\ (IF liveVersion = center2Snapshot
                THEN
                    /\ center2Snapshot = liveVersion
                    /\ Section = Center2
                ELSE
                    /\ Section #<1
                )
            )

OccupancyWithinCap ==
    occupancy <= Capacity

====