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
#!
DeclareGlobalFunction("AllSOTGroups");
#! @Description
#!  computes the list of isomorphism classes of groups of order $n$.

#! @BeginExampleSession
#! gap> AllSOTGroups(3*5*7*11);
#! [ <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators>,
#!  <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators> ]
#! @EndExampleSession

#!
DeclareGlobalFunction("SOTGroup");
#! @Description
#!  returns the $i$-th group of order $n$ in the list.
#!
DeclareGlobalFunction("NumberOfSOTGroups");
#! Description
#!  returns the number of isomorphism types of groups of order $n$.

#!
DeclareGlobalFunction("IdSOTGroup");
#! @Description
#!  determines the SOT library number of $G$; that is, the function returns a pair [order, i] where $G$ is isomorphic to SOTGroup( order, i ).

#!
DeclareGlobalFunction("SOTGroupIsAvailable");
#! @Description
#!  returns true if the order is covered in the SOTGrps package.

#!
DeclareGlobalFunction("SOTGroupsInformation");
