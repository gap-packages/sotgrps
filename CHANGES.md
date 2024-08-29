This file describes changes in the `sotgrps` package.

# 1.3 (2024-08-29)

  - Ensure the presentations used by `AllSOTGroups(n)[i]` and `SOTGroup(n,i)`
    are identical, not just equivalent.
  - Integrated with the small groups library (SGL): for orders not already
    included in the SGL, we now extend the SGL commands for those orders.
    So commands like `NrSmallGroups`, `AllSmallGroups` or `IdGroup` will
    work e.g. for (groups of) order 7*13^3 when `sotgrps` is loaded.
  - Minor janitorial changes

# 1.2 (2023-06-20)

  - Fix warnings when loaded without the `polycyclic` package present
  - Fix some typos in the documentation
  - Minor janitorial changes

# 1.1 (2023-06-06)

  - First public release.
