# mysmallgrps_gap_pkg
The main function MySmallGroups(n) takes in a number that factorises into at most 4 primes, where p, q, r, s are distinct primes, and constructs all groups of order n, up to isomorphism. If a group is solvable, then it constructs the group by polycyclic presentations.

MySmallGroupsInformation(n) gives the number of the isomorphism types of groups of order n.
MySmallGroupsInformation() gives information of the available order types that MySmallGroups(n) applies to.

MySmallGroupIsAvailable(n) returns true if the groups of order n can be consrtcuted by MySmallGroups(n).
