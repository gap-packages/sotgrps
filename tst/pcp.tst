#@if IsPackageMarkedForLoading("polycyclic", "")
gap> LoadPackage("polycyclic", false);
true

#
gap> AllSOTGroups(60,IsPcpGroup);
[ Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], 
  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], 
  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 3, 5, 2, 2 ], 
  Pcp-group with orders [ 2, 2, 5, 3 ], Pcp-group with orders [ 2, 2, 3, 5 ], 
  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], 
  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], 
  Alt( [ 1 .. 5 ] ) ]

#
gap> SOTGroup(2*3*5*7, 1, IsPcpGroup);
Pcp-group with orders [ 2, 3, 5, 7 ]

#@fi
