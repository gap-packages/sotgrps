# sotgrps.pkg

This package is complementary to an MPhil thesis "Groups of small order type" and the joint paper "Groups whose order factorise into at most four primes" (Dietrich, Eick, & Pan, 2020) available at https://doi.org/10.1016/j.jsc.2021.04.005.

To use this package, if you have GAP installed, then please unzip the file into the pkg folder in GAP, and then simply run the command LoadPackage("sotgrps") in GAP; if you haven't installed GAP, you could find instruction on https://www.gap-system.org/Download/ to download and install GAP first.

The main user functions are given in the file SmallGrps.gi.

User functions:

NumberOfSOTGroups(n)   : returns the number of isomorphism types of groups of order n.

AllSOTGroups(n)        :takes in a number n that factorises into at most 4 primes or of the form p^4q (p, q are distinct primes), and outputs a list of all groups of order n, up to isomorphism. If a group is solvable, then it constructs the group using refined polycyclic presentations. Upon construction, we check consistency of the pcgs and relators, to remove such tests, change "USE_NC := true" to "USE_NC := false" in the sot.gi file; we construct solvable groups using polycyclic presentations and use PcpGroupToPcGroup to convert them from PcpGroup to PcGroup, if PcpGroup is preferred, change "USE_PCP := false" into "USE_PCP := true" in the sot.gi file.

SOTGroup(n, i)         : returns the i-th group with respect to the ordering of the list AllSOTGroups(n) without constructing all groups in the list.

IdSOTGroup(G)          : returns false if G is not a group or |G| is not available; otherwise returns the SOT-group ID (n, i), where n = |G| and G is isomorphic to SOTGroup(n, i).

SOTGroupIsAvailable(n) : returns true if the groups of order n are available.
SOTGroupsInformation(n): returns a brief comment on the enumeration of the isomorphism types of groups of order n.
SOTGroupsInformation() : returns information of the available order types that AllSOTGroups(n) applies to.


Note that the construction of small groups could be different to the existing library, for which reason the list of groups for a given order may not have the same order as enumerated by the IdGroup/IdSmallGroup function.

In particular, with SOTGroup(n, i), we construct the i-th group of order n in our SOT-group list.

IdSOTGroup(group) returns the group ID in line with SOTGroup(n, i), namely, the position of the input group of order n in the list constructed by AllSOTGroups(n).

References:
[1] X. Pan, Groups of small order type. MPhil thesis at Monash University.

[2] H. Dietrich, B. Eick, & X. Pan, Groups whose order factorise into at most four primes. In: Journal of Symbolic Computation (108) (2022), pp. 23–40. (https://doi.org/10.1016/j.jsc.2021.04.005)

[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/xpan-eileen/sotgrps_gap_pkg/HEAD)

.. image:: https://mybinder.org/badge_logo.svg
 :target: https://mybinder.org/v2/gh/xpan-eileen/sotgrps_gap_pkg/HEAD
