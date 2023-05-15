#############################################################################
#! @Chapter The SOTGrps package
#! With some overlaps, the SOTGrps package extends the Small Group Library to give access to some more
#!    "small" orders. For example, it constructs a
#!    complete and irredundant list of isomorphism type representatives of the groups of order
#!    - that factorises into at most four primes;
#!    - p^4q, for any primes p and q.
##

###############################
##
##
##
#! @Section Main functions
#! @Description
#!  computes the list of isomorphism classes of groups of order <A>n</A>.
#! Solvable groups are given as PcGroup, unless USE_PCP is turned on, in which case the groups are constructed as PcpGroup.
#! Nonsolvable groups are given
#! @Arguments n
#! @BeginExampleSession
#! gap> AllSOTGroups(3*5*7*11);
#! [ <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators>,
#!  <pc group of size 1155 with 4 generators>, <pc group of size 1155 with 4 generators> ]
#! @EndExampleSession
DeclareGlobalFunction("AllSOTGroups");

#! @Description
#!  returns the <A>i</A>-th group of order <A>n</A> in the list.
#! @Arguments n, i
DeclareGlobalFunction("SOTGroup");

#! Description
#!  returns the number of isomorphism types of groups of order <A>n</A>.
#! @Arguments n
#
DeclareGlobalFunction("NumberOfSOTGroups");
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
