This file describes changes in the `sotgrps` package.

# 1.3.1 (2026-07-29)

  - Declare `SmallGrp` as a needed package. It always was required, as
    `gap/Integration.gi` extends the small groups library, but this used
    to be masked by `SmallGrp` being loaded by default.

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
