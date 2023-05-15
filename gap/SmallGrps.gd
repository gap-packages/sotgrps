#############################################################################
#! @Chapter The SOTGrps Library
#! With some overlaps, the SOTGrps library extends the Small Group Library to give access to some more
    "small" orders. For example, in addition to the existing Small Groups Library, it constructs a
    complete and irredundant list of isomorphism type representatives of the groups of order
    - that factorises into at most four primes;
    - p^4q.
##
##

###############################
##
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
#!  returns the <A>i</A>-th group of order <A>n</A> in the list.
#! @Arguments n, i
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
