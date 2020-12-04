# sotgrps.pkg
# sotsmallgrps

To use this package, if you have GAP installed, then please unzip the file into the pkg folder in GAP, and then simply run the command LoadPackage("sotgrps") in GAP; if you haven't installed GAP, you could find instruction on https://www.gap-system.org/Download/ to download and install GAP first.

The main function AllSOTGroups(n) takes in a number n that factorises into at most 4 primes or of the form p^4q (p, q are distinct primes), and constructs all groups of order n, up to isomorphism. If a group is solvable, then it constructs the group using refined polycyclic presentations. Upon construction, we check consistency of the pcgs and relators, to remove such tests, change "USE_NC := true" to "USE_NC := false" in the sot.gi file; we construct solvable groups using polycyclic presentations and use PcpGroupToPcGroup to convert them from PcpGroup to PcGroup, if PcpGroup is preferred, change "USE_PCP := false" into "USE_PCP := true" in the sot.gi file.

SOTGroupIsAvailable(n) returns true if the groups of order n can be constructed by AllSOTGroups(n).

SOTGroupsInformation(n) gives the number of the isomorphism types of groups of order n.
SOTGroupsInformation() gives information of the available order types that AllSOTGroups(n) applies to.

Note that the construction of small groups could be different to the existing library, for which reason the list of groups for a given order may not have the same order as enumerated by the IdGroup/IdSmallGroup function.

In particular, with SOTGroup(n, i), we construct the i-th group of order n in our list.

IdSOTGroup(group) returns the group ID in line with SOTGroup(n, i), namely, the position of the input group of order n in the list constructed by AllSOTGroups(n).
