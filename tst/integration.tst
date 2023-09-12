#
gap> START_TEST("integration.tst");

#
gap> testOrder:=function(n)
>   local G, H, d, i;
>   d := NrSmallGroups(n);
>   for i in [1..d] do
>     G:=SmallGroup(n, i);
>     H:=PcGroupCode(CodePcGroup(G), n);
>     Assert(0, not HasIdGroup(H));
>     if IdGroup(H) <> [n,i] then
>       Error("failure at ", [n,i]);
>     fi;
>   od;
>   SmallGroupsInformation(n);
> end;;

#
gap> testOrder(13^3*2);

  There are 15 groups of order 4394.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 13-subgroup and a
        normal Sylow 2-subgroup.
    6 is non-nilpotent and has a normal Sylow 2-subgroup with Sylow 
       13-subgroup [ 2197, 1 ].
    7 - 9 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow 
       13-subgroup [ 2197, 2 ].
    10 - 12 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow 
       13-subgroup [ 2197, 5 ].
    13 - 14 are non-nilpotent and have a normal Sylow 2-subgroup with Sylow 
       13-subgroup [ 2197, 3 ].
    15 is non-nilpotent and has a normal Sylow 2-subgroup with Sylow 
       13-subgroup [ 2197, 4 ].

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 
gap> testOrder(13^3*3);

  There are 19 groups of order 6591.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 13-subgroup and a
        normal Sylow 3-subgroup.
    6 is non-nilpotent and has a normal Sylow 3-subgroup with Sylow 
       13-subgroup [ 2197, 1 ].
    7 - 10 are non-nilpotent and have a normal Sylow 3-subgroup with Sylow 
       13-subgroup [ 2197, 2 ].
    11 - 15 are non-nilpotent and have a normal Sylow 3-subgroup with Sylow 
       13-subgroup [ 2197, 5 ].
    16 - 18 are non-nilpotent and have a normal Sylow 3-subgroup with Sylow 
       13-subgroup [ 2197, 3 ].
    19 is non-nilpotent and has a normal Sylow 3-subgroup with Sylow 
       13-subgroup [ 2197, 4 ].

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 
gap> testOrder(13^3*5);

  There are 5 groups of order 10985.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 13-subgroup and a
        normal Sylow 5-subgroup.

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 
gap> testOrder(13^3*7);

  There are 7 groups of order 15379.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 13-subgroup and a
        normal Sylow 7-subgroup.
    6 is non-nilpotent and has a normal Sylow 7-subgroup with Sylow 
       13-subgroup [ 2197, 5 ].
    7 is non-nilpotent and has a normal Sylow 7-subgroup with Sylow 
       13-subgroup [ 2197, 3 ].

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 
gap> testOrder(13^3*11);

  There are 5 groups of order 24167.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 13-subgroup and a
        normal Sylow 11-subgroup.

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 
gap> testOrder(37^3*7);

  There are 6 groups of order 354571.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 3 are abelian.
    4 - 5 are nonabelian nilpotent and have a normal Sylow 37-subgroup and a
        normal Sylow 7-subgroup.
    6 is non-nilpotent and has a normal Sylow 7-subgroup with Sylow 
       37-subgroup [ 50653, 5 ].

  This size belongs to layer 12 of the SmallGroups library. 
  IdSmallGroup is available for this size. 
 

#
gap> STOP_TEST("integration.tst", 1);
