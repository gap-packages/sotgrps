#############################################################################
##
#W  SmallGrps.gd
##
##

###############################
#F  SmallGroups( n )
##
##
##
#! @Description
#!  Compute the list of isomorphism classes of groups of order $n$.
#!
DeclareGlobalFunction("AllSOTGroups");
#! @BeginExampleSession
#! gap> AllSOTGroups(3*5*7*11);
#! [ <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators>,
#!  <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators> ]
#! @EndExampleSession

#!
DeclareGlobalFunction("SOTGroup");

#!
DeclareGlobalFunction("NumberOfSOTGroups");

#!
DeclareGlobalFunction("SOTGroupIsAvailable");

#!
DeclareGlobalFunction("SOTGroupsInformation");

#!
DeclareGlobalFunction("IdSOTGroup");
