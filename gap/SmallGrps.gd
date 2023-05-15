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
#! Nonsolvable groups are given as permutation groups.
#! @Arguments n
#! @BeginExampleSession
#! gap> AllSOTGroups(60);
#! [ <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!  <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!  <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!  Alt( [ 1 .. 5 ] ) ]

#! gap> USE_PCP := true;;
#! gap> AllSOTGroups(60);
#! [ Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ],
#!  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 3, 5, 2, 2 ], Pcp-group with orders [ 2, 2, 5, 3 ], Pcp-group with orders [ 2, 2, 3, 5 ],
#!  Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ], Pcp-group with orders [ 2, 2, 3, 5 ],
#! Alt( [ 1 .. 5 ] ) ]
#! @EndExampleSession
DeclareGlobalFunction("AllSOTGroups");

#! @Description
#!  returns the <A>i</A>-th group of order <A>n</A> in the list.
#! @Arguments n, i
#! @BeginExampleSession
#! gap> SOTGroup(2*3*5*7, 1);
#! <pc group of size 210 with 4 generators>
#! @EndExampleSession
DeclareGlobalFunction("SOTGroup");

#! @Description
#!  returns the number of isomorphism types of groups of order <A>n</A>.
#! @Arguments n
#! @BeginExampleSession
#! gap> NumberOfSOTGroups(2*3*5*7);
#! 12
#! @EndExampleSession
DeclareGlobalFunction("NumberOfSOTGroups");

#! @Description
#!  determines the SOT library number of <A>G</A>;
#!  that is, the function returns a pair [<A>n</A>, <A>i</A>] where <A>G</A> is isomorphic to SOTGroup(<A>n</A>, <A>i</A>).
#! @Arguments G
DeclareGlobalFunction("IdSOTGroup");

#! @Description
#!  returns <K>true</K> if the order <A>n</A> is available in the SOTGrps library, and <K>false</K> otherwise.
#! @Arguments n
DeclareGlobalFunction("SOTGroupIsAvailable");

#!
DeclareGlobalFunction("SOTGroupsInformation");
