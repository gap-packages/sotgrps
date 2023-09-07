#
gap> START_TEST("SOTGroupsInformation.tst");

#
gap> SOTGroupsInformation(5);

  There is 1 group of order 5.

  There is 1 cyclic group.

#
gap> SOTGroupsInformation(5^2);

  There are 2 groups of order 25.

  There is 1 cyclic group, and 1 elementary abelian group.

#
gap> SOTGroupsInformation(5^3);

  There are 5 groups of order 125.

  There are 3 abelian groups, and 2 extraspecial groups.

#
gap> SOTGroupsInformation(5^4);

  There are 15 groups of order 625.

  There are 5 abelian groups, and 10 nonabelian groups.

#
gap> SOTGroupsInformation(5*3);

  There is 1 group of order 15.

  There is 1 cyclic group.

#
gap> SOTGroupsInformation(5*11);

  There are 2 groups of order 55.

  There is 1 cyclic group, and 1 nonabelian group.

#
gap> SOTGroupsInformation(5^2*3);

  There are 3 groups of order 75.

  There are 2 abelian groups.

#
gap> SOTGroupsInformation(5^3*3);

  There are 7 groups of order 375.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 3 are abelian.
    SOT 4 - 5 are nonabelian nilpotent and have a normal Sylow 5-subgroup and
            a normal Sylow 3-subgroup.
    SOT 6 is non-nilpotent and has a normal Sylow 3-subgroup with Sylow 
           5-subgroup [ 125, 5 ].
    SOT 7 is non-nilpotent and has a normal Sylow 3-subgroup with Sylow 
           5-subgroup [ 125, 3 ].

#
gap> SOTGroupsInformation(5^4*3);

  There are 21 groups of order 1875.

  The groups of order p^4q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 15 are nilpotent and all Sylow subgroups are normal.
    SOT 16 is sovable, non-nilpotent and has a normal abelian Sylow 5-subgroup
           [ 625, 2 ], with cyclic Sylow 3-subgroup.
    SOT 17 is sovable, non-nilpotent and has a normal abelian Sylow 5-subgroup
           [ 625, 11 ], with cyclic Sylow 3-subgroup.
    SOT 18 - 19 are sovable, non-nilpotent and have a normal elementary
            abelian Sylow 5-subgroup [ 625, 15 ], with cyclic Sylow 
           3-subgroup.
    SOT 20 is sovable, non-nilpotent and has a normal nonabelian Sylow 
           5-subgroup [ 625, 14 ], with cyclic Sylow 3-subgroup.
    SOT 21 is sovable, non-nilpotent and has a normal nonabelian Sylow 
           5-subgroup [ 625, 12 ], with cyclic Sylow 3-subgroup.

#
gap> SOTGroupsInformation(5^2*3^2);

  There are 6 groups of order 225.

  The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 4 are abelian and all Sylow subgroups are normal.
    SOT 5 is non-abelian, non-nilpotent and has a normal Sylow 5-subgroup 
           [ 25, 2 ] with Sylow 3-subgroup [ 9, 1 ].
    SOT 6 is non-abelian, non-nilpotent and has a normal Sylow 5-subgroup 
           [ 25, 2 ] with Sylow 3-subgroup [ 9, 2 ].

#
gap> SOTGroupsInformation(5^2*11^2);

  There are 15 groups of order 3025.

  The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 4 are abelian and all Sylow subgroups are normal.
    SOT 5 is non-abelian, non-nilpotent and has a normal Sylow 11-subgroup 
           [ 121, 1 ] with Sylow 5-subgroup [ 25, 1 ].
    SOT 6 is non-abelian, non-nilpotent and has a normal Sylow 11-subgroup 
           [ 121, 1 ] with Sylow 5-subgroup [ 25, 2 ].
    SOT 7 - 10 are non-abelian, non-nilpotent and have a normal Sylow 
           11-subgroup [ 121, 2 ] with Sylow 5-subgroup [ 25, 1 ].
    SOT 11 - 15 are non-abelian, non-nilpotent and have a normal Sylow 
           11-subgroup [ 121, 2 ] with Sylow 5-subgroup [ 25, 2 ].

#
gap> SOTGroupsInformation(5^2*3*11);

  There are 5 groups of order 825.

  The groups of order p^2qr are either solvable or isomorphic to Alt(5).
  The solvable groups are sorted by their Fitting subgroup.
    SOT 1 - 2 are the nilpotent groups.
    SOT 3 has Fitting subgroup of order 275.
    SOT 4 - 5 have Fitting subgroup of order 165.

#
gap> SOTGroupsInformation(13^3*3);

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

#
gap> SOTGroupsInformation(255025);

  There are 32 groups of order 255025.

  The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    1 - 4 are abelian and all Sylow subgroups are normal.
    5 - 6 are non-abelian, non-nilpotent and have a normal Sylow 101-subgroup 
       [ 10201, 1 ] with Sylow 5-subgroup [ 25, 1 ].
    7 is non-abelian, non-nilpotent and has a normal Sylow 101-subgroup 
       [ 10201, 1 ] with Sylow 5-subgroup [ 25, 2 ].
    8 - 27 are non-abelian, non-nilpotent and have a normal Sylow 101-subgroup
       [ 10201, 2 ] with Sylow 5-subgroup [ 25, 1 ].
    28 - 32 are non-abelian, non-nilpotent and have a normal Sylow 
       101-subgroup [ 10201, 2 ] with Sylow 5-subgroup [ 25, 2 ].

#
gap> SOTGroupsInformation(2^3*3);

  There are 15 groups of order 24.

  The groups of order p^3q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 3 are abelian.
    SOT 4 - 5 are nonabelian nilpotent and have a normal Sylow 2-subgroup and
            a normal Sylow 3-subgroup.
    SOT 6 is non-nilpotent and has a normal Sylow 2-subgroup [ 8, 1 ].
    SOT 7 - 8 are non-nilpotent and have a normal Sylow 2-subgroup [ 8, 2 ].
    SOT 9 is non-nilpotent and has a normal Sylow 2-subgroup [ 8, 5 ].
    SOT 10 - 11 are non-nilpotent and have a normal Sylow 2-subgroup [ 8, 3 ].
    SOT 12 is non-nilpotent and has a normal Sylow 2-subgroup [ 8, 4 ].
    SOT 13 is non-nilpotent and has a normal Sylow 3-subgroup with Sylow 
           2-subgroup [ 8, 5 ].
    SOT 15 is non-nilpotent, isomorphic to Sym(4), and has no normal Sylow
            subgroups.

#
gap> SOTGroupsInformation(2^2*3^2);

  There are 14 groups of order 36.

  The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 4 are abelian and all Sylow subgroups are normal.
    SOT 5 is non-abelian, non-nilpotent and has a normal Sylow 3-subgroup 
           [ 9, 1 ] with Sylow 2-subgroup [ 4, 1 ].
    SOT 6 is non-abelian, non-nilpotent and has a normal Sylow 3-subgroup 
           [ 9, 1 ] with Sylow 2-subgroup [ 4, 2 ].
    SOT 7 is non-abelian, non-nilpotent and has a normal Sylow 2-subgroup [4,
            2] with Sylow 3-subgroup [9, 1].
    SOT 8 - 10 are non-abelian, non-nilpotent and have a normal Sylow 
           3-subgroup [ 9, 2 ] with Sylow 2-subgroup [ 4, 1 ].
    SOT 11 - 14 are non-abelian, non-nilpotent and have a normal Sylow 
           3-subgroup [ 9, 2 ] with Sylow 2-subgroup [ 4, 1 ].

#
gap> SOTGroupsInformation(2^4*3);

  There are 52 groups of order 48.

  The groups of order p^4q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 14 are nilpotent and all Sylow subgroups are normal.
    SOT 15 is sovable, non-nilpotent and has a normal Sylow 3-subgroup, with
            cylic Sylow 2-subgroup [ 16, 1 ].
    SOT 16 - 17 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with abelian Sylow 2-subgroup [ 16, 5 ].
    SOT 18 is sovable, non-nilpotent and has a normal Sylow 3-subgroup, with
            abelian Sylow 2-subgroup [ 16, 2 ].
    SOT 19 - 20 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with abelian Sylow 2-subgroup [ 16, 10 ].
    SOT 21 is sovable, non-nilpotent and has a normal Sylow 3-subgroup, with
            elementary abelian Sylow 2-subgroup [ 16, 14 ].
    SOT 22 - 24 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 13 ].
    SOT 25 - 27 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 11 ].
    SOT 28 - 29 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 3 ].
    SOT 30 - 31 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 12 ].
    SOT 32 - 33 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 4 ].
    SOT 34 - 35 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 6 ].
    SOT 36 - 38 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 8 ].
    SOT 39 - 40 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 7 ].
    SOT 41 - 42 are sovable, non-nilpotent and have a normal Sylow 3-subgroup,
           with nonabelian Sylow 2-subgroup [ 16, 9 ].
    SOT 43 is sovable, non-nilpotent and has a normal abelian Sylow 2-subgroup
           [ 16, 2 ], with cyclic Sylow 3-subgroup.
    SOT 44 is sovable, non-nilpotent and has a normal abelian Sylow 2-subgroup
           [ 16, 10 ], with cyclic Sylow 3-subgroup.
    SOT 45 - 46 are sovable, non-nilpotent and have a normal elementary
            abelian Sylow 2-subgroup [ 16, 14 ], with cyclic Sylow 3-subgroup.
    SOT 47 is sovable, non-nilpotent and has a normal nonabelian Sylow 
           2-subgroup [ 16, 13 ], with cyclic Sylow 3-subgroup.
    SOT 48 is sovable, non-nilpotent and has a normal nonabelian Sylow 
           2-subgroup [ 16, 12 ], with cyclic Sylow 3-subgroup.
    SOT 49 - 52 are solvable, non-nilpotent, and have no normal Sylow
            subgroups.

#
gap> SOTGroupsInformation(3^4*13);

  There are 51 groups of order 1053.

  The groups of order p^4q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 15 are nilpotent and all Sylow subgroups are normal.
    SOT 16 is sovable, non-nilpotent and has a normal Sylow 13-subgroup, with
            cylic Sylow 3-subgroup [ 81, 1 ].
    SOT 17 - 18 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with abelian Sylow 3-subgroup [ 81, 5 ].
    SOT 19 is sovable, non-nilpotent and has a normal Sylow 13-subgroup, with
            abelian Sylow 3-subgroup [ 81, 2 ].
    SOT 20 - 21 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with abelian Sylow 3-subgroup [ 81, 11 ].
    SOT 22 is sovable, non-nilpotent and has a normal Sylow 13-subgroup, with
            elementary abelian Sylow 3-subgroup [ 81, 15 ].
    SOT 23 - 25 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 14 ].
    SOT 26 - 28 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 6 ].
    SOT 29 - 32 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 13 ].
    SOT 33 - 34 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 3 ].
    SOT 35 - 37 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 4 ].
    SOT 38 - 39 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 12 ].
    SOT 40 - 42 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 8 ].
    SOT 43 - 44 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 9 ].
    SOT 45 - 47 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 7 ].
    SOT 48 - 49 are sovable, non-nilpotent and have a normal Sylow 
           13-subgroup, with nonabelian Sylow 3-subgroup [ 81, 10 ].
    SOT 50 is sovable, non-nilpotent and has a normal elementary abelian Sylow
           3-subgroup [ 81, 15 ], with cyclic Sylow 13-subgroup.
    SOT 51 is solvable, non-nilpotent, and has no normal Sylow subgroups.

#
gap> SOTGroupsInformation(2^2*3*5);

  There are 13 groups of order 60.

  The groups of order p^2qr are either solvable or isomorphic to Alt(5).
  The solvable groups are sorted by their Fitting subgroup.
    SOT 1 - 2 are the nilpotent groups.
    SOT 3 - 5 have Fitting subgroup of order 15.
    SOT 6 has Fitting subgroup of order 20.
    SOT 7 - 12 have Fitting subgroup of order 30.
    SOT 13 is nonsolvable and has Fitting subgroup of order 1.

#
gap> SOTGroupsInformation(3^4*5);

  There are 16 groups of order 405.

  The groups of order p^4q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 15 are nilpotent and all Sylow subgroups are normal.
    SOT 16 is sovable, non-nilpotent and has a normal elementary abelian Sylow
           3-subgroup [ 81, 15 ], with cyclic Sylow 5-subgroup.

#
gap> SOTGroupsInformation(2^4*17);

  There are 54 groups of order 272.

  The groups of order p^4q are solvable by Burnside's pq-Theorem.
  These groups are sorted by their Sylow subgroups.
    SOT 1 - 14 are nilpotent and all Sylow subgroups are normal.
    SOT 15 - 18 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with cylic Sylow 2-subgroup [ 16, 1 ].
    SOT 19 - 23 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with abelian Sylow 2-subgroup [ 16, 5 ].
    SOT 24 - 25 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with abelian Sylow 2-subgroup [ 16, 2 ].
    SOT 26 - 28 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with abelian Sylow 2-subgroup [ 16, 10 ].
    SOT 29 is sovable, non-nilpotent and has a normal Sylow 17-subgroup, with
            elementary abelian Sylow 2-subgroup [ 16, 14 ].
    SOT 30 - 32 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 13 ].
    SOT 33 - 35 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 11 ].
    SOT 36 - 38 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 3 ].
    SOT 39 - 40 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 12 ].
    SOT 41 - 43 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 4 ].
    SOT 44 - 47 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 6 ].
    SOT 48 - 50 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 8 ].
    SOT 51 - 52 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 7 ].
    SOT 53 - 54 are sovable, non-nilpotent and have a normal Sylow 
           17-subgroup, with nonabelian Sylow 2-subgroup [ 16, 9 ].

#
gap> SOTGroupsInformation(19*23*29*31);

  There is 1 group of order 392863.

  All groups of order 392863 are abelian.

#
gap> SOTGroupsInformation(11*23*29*31);

  There are 2 groups of order 227447.

  The groups of order pqrs are solvable and classified by O. H"older.
  These groups are sorted by their centre.
    SOT 1 is abelian.
    SOT 2 has centre of order that is a product of two distinct primes.

#
gap> SOTGroupsInformation(3*7*43*3613);

  There are 61 groups of order 3262539.

  The groups of order pqrs are solvable and classified by O. H"older.
  These groups are sorted by their centre.
    SOT 1 is abelian.
    SOT 2 - 7 have centre of order that is a product of two distinct primes.
    SOT 8 - 23 have a cyclic centre of prime order.
    SOT 24 - 61 have a trivial centre.

#
gap> STOP_TEST("SOTGroupsInformation.tst", 1);
