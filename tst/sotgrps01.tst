# SOTGrps, chapter 1
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST("sotgrps01.tst");

# doc/_Chapter_The_SOTGrps_package.xml:29-42
gap> AllSOTGroups(60);
[ <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
 <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
 <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
 Alt( [ 1 .. 5 ] ) ]
gap> USE_PCP := true;;
gap> AllSOTGroups(60);
[ Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ],
 Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 3, 5, 2, 2 ], Pcp-group with orders [ 2, 2, 5, 3 ], Pcp-group with orders [ 2, 2, 3, 5 ],
 Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ],
 Alt( [ 1 .. 5 ] ) ]
gap> USE_PCP := false;;

# doc/_Chapter_The_SOTGrps_package.xml:54-57
gap> SOTGroup(2*3*5*7, 1);
<pc group of size 210 with 4 generators>

# doc/_Chapter_The_SOTGrps_package.xml:68-73
gap> NumberOfSOTGroups(2*3*5*7);
12
gap> NumberOfSOTGroups(2*3*5*7*11);
Error, Order 2310 is not available

# doc/_Chapter_The_SOTGrps_package.xml:110-135
gap> SOTGroupsInformation(2^2*3*19);

  There are 15 groups of order 228.

  The groups of order p^2qr are either solvable or isomorphic to Alt(5).
  The solvable groups are sorted by their Fitting subgroup.
     SOT 1 - 2 are the nilpotent groups.
     SOT 3 has Fitting subgroup of order 57.
     SOT 4 - 7 have Fitting subgroup of order 76.
     SOT 8 - 9 have Fitting subgroup of order 38.
     SOT 10 - 15 have Fitting subgroup of order 114.
gap> SOTGroupsInformation(2662);

  There are 15 groups of order 2662.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
     SOT 1 - 3 are abelian.
     SOT 4 - 5 are nonabelian nilpotent and have a normal Sylow 11-subgroup and a normal Sylow 2-subgroup.
     SOT 6 is non-nilpotent and has a normal Sylow 2-subgroup [ 2, 1 ] with Sylow 11-subgroup [ 1331, 1 ].
     SOT 7 - 9 are non-nilpotent and have a normal Sylow 2-subgroup [ 2, 1 ] with Sylow 11-subgroup [ 1331, 2 ].
     SOT 10 - 12 are non-nilpotent and have a normal Sylow 2-subgroup [ 2, 1 ] with Sylow 11-subgroup [ 1331, 5 ].
     SOT 13 - 14 are non-nilpotent and have a normal Sylow 2-subgroup [ 2, 1 ] with Sylow 11-subgroup [ 1331, 3 ].
     SOT 15 is non-nilpotent and has a normal Sylow 2-subgroup [ 2, 1 ] with Sylow 11-subgroup [ 1331, 4 ].

#
gap> STOP_TEST("sotgrps01.tst", 1);
