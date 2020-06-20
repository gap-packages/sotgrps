# mysmallgrps_gap_pkg
The main function MySmallGroups(n) takes in a number that factorises into at most 4 primes, where p, q, r, s are distinct primes, and constructs all groups of order n, up to isomorphism. If a group is solvable, then it constructs the group by polycyclic presentations.

MySmallGroupsInformation(n) gives the number of the isomorphism types of groups of order n.
MySmallGroupsInformation() gives information of the available order types that MySmallGroups(n) applies to.

Note that the construction of small groups could be different to the existing library, for which reason the list of groups for a given order may not have the same order as enumerated by the IdGroup/IdSmallGroup function.

In particular, with MySmallGroup(n, i), we construct the i-th group of order n in our list.

MySmallGroupIsAvailable(n) returns true if the groups of order n can be constructed by MySmallGroups(n).

MyIdSmallGroup(group) returns the group ID in line with MySmallgroup(n, i), and the list given by MySmallGroups(n) for groups of order n. 
