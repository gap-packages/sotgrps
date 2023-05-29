[![CI](https://github.com/gap-packages/sotgrps/actions/workflows/CI.yml/badge.svg)](https://github.com/gap-packages/sotgrps/actions/workflows/CI.yml)
[![codecov](https://codecov.io/gh/gap-packages/sotgrps/branch/master/graph/badge.svg)](https://codecov.io/gh/gap-packages/sotgrps)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/gap-packages/sotgrps_gap_pkg/HEAD)

# SOTGrps

This package for the [GAP computer algebra system](https://www.gap-system.org)
is complementary to an MPhil thesis "Groups of small order type" and the
joint paper "Groups whose order factorise into at most four primes"
(Dietrich, Eick, & Pan, 2020) available at
<https://doi.org/10.1016/j.jsc.2021.04.005>.

Using this package requires GAP, you can get it from
<https://www.gap-system.org/Download/>. If you have GAP installed, then
please unzip the file into the pkg folder in GAP, and then simply run
the command `LoadPackage("sotgrps")` in GAP.

The main user functions are given in the file `SOTGrps.gi`.

User functions:

- `NumberOfSOTGroups(n)`: returns the number of isomorphism types of
groups of order `n`.

- `AllSOTGroups(n)`: takes in a number `n` that factorises into at most
4 primes or of the form `p^4q` (`p`, `q` are distinct primes), and
outputs a complete and duplicate-free list of isomorphism class
representatives of the groups of order `n`. If a group is solvable, then
it constructs the group using refined polycyclic presentations;
otherwise the group is given as a permutation group.

- `SOTGroup(n, i)`: returns the `i`-th group with respect to the ordering
of the list `AllSOTGroups(n)` without constructing all groups in the list.

- `IdSOTGroup(G)`: returns false if G is not a group or |G| is not
available; otherwise returns the SOT-group ID (n, i), where n = |G| and
G is isomorphic to `SOTGroup(n, i)`.

- `IsSOTAvailable(n)`: returns true if the groups of order n are
available.

- `SOTGroupsInformation(n)`: returns a brief comment on the
enumeration of the isomorphism types of groups of order `n`.



Note that the construction of small groups could be different to the
existing library, for which reason the list of groups for a given order
may not have the same order as enumerated by the `IdGroup` /
`IdSmallGroup` function.

In particular, with `SOTGroup(n, i)`, we construct the `i`-th group of
order `n` in our SOT-group list.

`IdSOTGroup(group)` returns the group ID in line with `SOTGroup(n, i)`,
namely, the position of the input group of order n in the list
constructed by `AllSOTGroups(n)`.

## References

[1] X. Pan, Groups of small order type. MPhil thesis at Monash
University. <https://xpan-eileen.github.io/documents/Thesis_Groups_of_small_order_type.pdf>

[2] H. Dietrich, B. Eick, & X. Pan, Groups whose order factorise into at
most four primes. In: Journal of Symbolic Computation (108) (2022), pp.
23–40. <https://doi.org/10.1016/j.jsc.2021.04.005>

## License

The SOTGrps package is free software; you can redistribute and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at
your opinion) any later version.

The SOTGrps package is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.
