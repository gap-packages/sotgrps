#############################################################################
#! @Chapter The &SOTGrps; package
#! With some overlaps, the &SOTGrps; package extends the Small Group Library to give access to some more
#!    <Q>small</Q> orders. For example, it constructs a
#!    complete and irredundant list of isomorphism type representatives of the groups of order
#!    - that factorises into at most four primes;
#!    - <M>p^4q</M>, for distinct primes <M>p</M> and <M>q</M>.
#!
#! The mathematical background for this package is described in <Cite Key="DEP22"/>.

###############################
##
##
##
#! @Section Main functions
#!
#! In addition to the functions described below, the &SOTGrps; package also extends the
#! the Small Groups Library as provided by the &SmallGrp; package: with &SOTGrps; loaded,
#! functions such as <C>NumberSmallGroups</C>, <C>SmallGroup</C> or <C>IdGroup</C>
#! will work for orders support by &SOTGrps; but not by &SmallGrp;.
#!
#! Note: for orders support by &SOTGrps; *and* by &SmallGrp;, the respective ids as
#! produced by <C>IdGroup</C> versus <C>IdSOTGroup</C> in general do not agree.
#! In a future version we may provided functions to convert between them.

#! @Description
#!  takes in a number <A>n</A> that factorises into at most four primes or is of the form <M>p^4q</M> (<M>p</M>, <M>q</M> are distinct primes),
#!  and returns a complete and duplicate-free list of isomorphism class representatives of the groups of order <A>n</A>.
#!  Solvable groups are using refined polycyclic presentations.
#!  By default, solvable groups are constructed in the filter <C>IsPcGroup</C>,
#!  but if the optional argument <A>filter</A> is set to <C>IsPcpGroup</C> then
#!  the groups are constructed in that filter instead.
#!  Nonsolvable groups are always returned as permutation groups.
#! @Arguments n [, filter]
#! @BeginExampleSession
#! gap> AllSOTGroups(60);
#! [ <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!   <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!   <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!   <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!   <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!   <pc group of size 60 with 4 generators>, <pc group of size 60 with 4 generators>,
#!  Alt( [ 1 .. 5 ] ) ]
#! @EndExampleSession
DeclareGlobalFunction("AllSOTGroups");

#! @Description
#!  takes in a number <A>n</A> that factorises into at most four primes or of the form <M>p^4q</M> (<M>p</M>, <M>q</M> are distinct primes),
#!  and returns the number of isomorphism types of groups of order <A>n</A>.
#! @Arguments n
#! @BeginExampleSession
#! gap> NumberOfSOTGroups(2*3*5*7);
#! 12
#! gap> NumberOfSOTGroups(2*3*5*7*11);
#! Error, Order 2310 is not supported by SOTGrps.
#! Please refer to the SOTGrps documentation for the list of supported orders.
#! @EndExampleSession
DeclareGlobalFunction("NumberOfSOTGroups");

#! @Description
#!  takes in a pair of numbers <A>n, i</A>, where <A>n</A> factorises into at most four primes or of the form <M>p^4q</M> (<M>p</M>, <M>q</M> are distinct primes),
#!  and returns the <A>i</A>-th group with respect to the ordering of
#!  the list <C>AllSOTGroups(<A>n</A>)</C> without constructing all groups in the list.
#!  The option of constructing a PcpGroup is available for solvable groups.
#! @Arguments n, i[, arg]
#! @BeginExampleSession
#! gap> SOTGroup(2*3*5*7, 1);
#! <pc group of size 210 with 4 generators>
#! @EndExampleSession
#!  If the input <A>i</A> exceeds the number of groups of order <A>n</A>, an error message is returned.
DeclareGlobalFunction("SOTGroup");

#! @Description
#!  takes in a group of order determines the SOT library number of <A>G</A>;
#!  that is, the function returns a pair [<A>n</A>, <A>i</A>] where <A>G</A> is isomorphic to <C>SOTGroup(<A>n</A>,<A>i</A>)</C>.
#!  Note that if the input group is a PcpGroup, this may result in slow runtime, as <C>IdSOTGroup</C> may compute the <C>Centre</C> and/or the <C>FittingSubgroup</C>,
#!  which is slow for PcpGroups.
#! @Arguments G
DeclareAttribute( "IdSOTGroup", IsGroup );

#! @Description
#! determines whether two groups <A>G</A>, <A>H</A> are isomorphic. It is assumed that the input groups are available in the &SOTGrps; library.
#! @Arguments G, H
#! @BeginExampleSession
#! gap> G:=Image(IsomorphismPermGroup(SmallGroup(690,1)));;
#! gap> H:=Image(IsomorphismPcGroup(SmallGroup(690,1)));;
#! gap> IsIsomorphicSOTGroups(G,H);
#! true
#! @EndExampleSession
DeclareGlobalFunction("IsIsomorphicSOTGroups");

#! @Description
#!  returns <K>true</K> if the order <A>n</A> is available in the &SOTGrps; library, and <K>false</K> otherwise.
#! @Arguments n
DeclareGlobalFunction("IsSOTAvailable");

#! @Description
#!  prints information on the groups of the specified order.
#!  Since there are some overlaps between the existing SmallGrps library and the &SOTGrps; library.
#!  In particular, &SOTGrps; may construct the groups in a different order and so generate a different group ID; we denote such IDs by <K>SOT</K>.
#!  If the order covered in &SOTGrps; library has no conflicts with the existing library, then such a flag is removed.
#! @BeginExampleSession
#! gap> SOTGroupsInformation(2^2*3*19);
#!
#!   There are 15 groups of order 228.
#!
#!   The groups of order p^2qr are either solvable or isomorphic to Alt(5).
#!   The solvable groups are sorted by their Fitting subgroup.
#!      SOT 1 - 2 are the nilpotent groups.
#!      SOT 3 has Fitting subgroup of order 57.
#!      SOT 4 - 7 have Fitting subgroup of order 76.
#!      SOT 8 - 9 have Fitting subgroup of order 38.
#!      SOT 10 - 15 have Fitting subgroup of order 114.
#!
#! gap> SOTGroupsInformation(2662);
#!
#!  There are 15 groups of order 2662.
#!
#!  The groups of order p^3q are solvable by Burnside's pq-Theorem.
#!  These groups are sorted by their Sylow subgroups.
#!    1 - 3 are abelian.
#!    4 - 5 are nonabelian nilpotent and have a normal Sylow 11-subgroup and a
#!        normal Sylow 2-subgroup.
#!    6 is non-nilpotent and has a normal Sylow 2-subgroup with Sylow
#!       11-subgroup [ 1331, 1 ].
#!    7 - 9 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow
#!       11-subgroup [ 1331, 2 ].
#!    10 - 12 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow
#!       11-subgroup [ 1331, 5 ].
#!    13 - 14 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow
#!       11-subgroup [ 1331, 3 ].
#!    15 is non-nilpotent and has a normal Sylow 2-subgroup with Sylow
 #!      11-subgroup [ 1331, 4 ].
#! @EndExampleSession
#! @Arguments n
DeclareGlobalFunction("SOTGroupsInformation");
