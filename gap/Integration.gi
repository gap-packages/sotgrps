## Integration with SmallGrps


# Get the next available "layer" id (the built-in library
# consists of 11 layers, but other packages may already have
# added further layers).
layer := Length(SMALL_AVAILABLE_FUNCS) + 1;

# Determine where to add our new lookup functions
pos := Maximum(List([
        SMALL_GROUP_FUNCS,
        SMALL_GROUPS_INFORMATION,
        NUMBER_SMALL_GROUPS_FUNCS,
        ID_GROUP_FUNCS,
        SELECT_SMALL_GROUPS_FUNCS,
    ], Length)) + 1;

#
# hook us up on the layer level
#

# meta data on small groups data we provide
SMALL_AVAILABLE_FUNCS[layer] := function( size )
    if size = 3^8 then
        return rec (
            lib := layer,
            func := pos,
            number := 123456    # number of groups of this order
        );
    fi;
end;

# meta data on IdGroup functionality we provide
ID_AVAILABLE_FUNCS[layer] := function( size )
    # Three possible implementations:

    # 1. No IdGroup functionality at all:
    return fail;

    # 2. IdGroup provided for all groups:
    #return SMALL_AVAILABLE_FUNCS[layer];

    # 3. IdGroup provided for a subset of order
    #if size in [ 12345, 67890 ] then
    #  return SMALL_AVAILABLE_FUNCS[layer];
    #fi;

end;

# Method for SmallGroup(size, i):
SMALL_GROUP_FUNCS[ pos ] := function( size, i, inforec )
    local g;

    # Now create the actual group
    Error("TODO");

    return g;
end;

# Method which selects a subset of all those groups with
# a certain combination of properties.
# A default method can be used; but more user friendly would be
# to install something custom which e.g. takes care of filtering
# the abelian groups, and which also knows that all groups
# of order p^n are nilpotent.
SELECT_SMALL_GROUPS_FUNCS[ pos ] := SELECT_SMALL_GROUPS_FUNCS[ 11 ];
#SELECT_SMALL_GROUPS_FUNCS[ pos ] := function( funcs, vals, inforec, all, id )
#    Error("TODO");
#end;

# Optional: Method for IdGroup(size, i).
ID_GROUP_FUNCS[ pos ] := function( G, inforec )
    Error("TODO");
end;

# Method for SmallGroupsInformation(size):
SMALL_GROUPS_INFORMATION[ pos ] := function( size, inforec, num )
    Print( " \n");
    Print( "      This database was created by BLA, see paper BLUB.\n");
    # TODO: add more
end;
```

# functions to convert AllSOTGroups output into SGL ordering
SOTRec.SGLordered := function(n)
  local groups, pos;
    if n in ordstodp then
      pos := Position(ordstodo, n);;
      groups := List(ids[pos], x->AllSOTGroups(n)[x]);;
    fi;
    return groups;
  end;


# p2qr or p2q2 orders up to 50 000 that need to change
ordstodo := [ 36, 100, 196, 225, 441, 484, 676, 1089, 1156, 1225, 1444, 1521, 2116, 2601, 3025, 3249, 3364, 3844, 4225, 4761, 5476, 5929, 6724, 7225, 7396, 7569, 8281, 8649, 8836, 9025,
  11236, 12321, 13225, 13924, 14161, 14884, 15129, 16641, 17689, 17956, 19881, 20164, 20449, 21025, 21316, 24025, 24964, 25281, 25921, 27556, 31329, 31684, 33489, 34225, 34969,
  37636, 40401, 40804, 41209, 42025, 42436, 43681, 45369, 45796, 46225, 47089, 47524, 47961, 48841 ];;
idstodo := [ [ 5, 1, 9, 6, 3, 7, 8, 2, 10, 13, 14, 11, 12, 4 ], [ 5, 1, 6, 7, 3, 8, 9, 2, 10, 13, 11, 12, 16, 14, 15, 4 ], [ 5, 1, 6, 3, 7, 8, 2, 9, 12, 10, 11, 4 ],
  [ 1, 3, 5, 2, 6, 4 ], [ 5, 1, 6, 3, 7, 8, 9, 2, 13, 10, 11, 12, 4 ], [ 5, 1, 6, 3, 7, 8, 2, 9, 12, 10, 11, 4 ], [ 5, 1, 6, 7, 3, 8, 9, 2, 10, 11, 12, 13, 16, 14, 15, 4 ],
  [ 1, 3, 5, 2, 6, 4 ], [ 5, 1, 6, 7, 3, 8, 9, 2, 10, 11, 12, 13, 16, 14, 15, 4 ], [ 1, 3, 2, 4 ], [ 5, 1, 6, 3, 7, 8, 2, 9, 12, 11, 10, 4 ],
  [ 5, 1, 6, 3, 7, 8, 9, 2, 13, 10, 11, 12, 4 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 12, 9, 11, 10 ], [ 1, 3, 2, 5, 4, 6, 7 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 10, 4, 15, 12, 11, 13, 14 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 10, 4, 11, 12, 14, 13, 15, 16, 17, 21, 18, 19, 20 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 11, 12, 13, 16, 15, 14 ],
  [ 1, 5, 3, 6, 2, 7, 8, 4, 12, 9, 11, 10 ], [ 1, 3, 2, 4 ], [ 1, 3, 2, 5, 4, 6 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 11, 12, 13, 16, 15, 14 ], [ 1, 3, 2, 4 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 11, 12, 14, 15 ], [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 5, 4, 6 ],
  [ 1, 3, 2, 5, 4, 6 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 4, 13, 10, 12, 11 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 5, 4, 6 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 11, 12, 14, 15 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 10, 4, 11, 16, 17, 21, 12, 14, 13, 15, 18, 19, 20 ],
  [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 12, 11, 14, 15 ], [ 1, 3, 2, 5, 4, 6 ],
  [ 1, 5, 3, 6, 2, 7, 8, 9, 4, 13, 10, 11, 12 ], [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 5, 4, 6 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ],
  [ 1, 3, 2, 4 ], [ 1, 3, 2, 5, 4, 6 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 11, 12, 14, 15 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 10, 4, 15, 11, 12, 13, 14 ],
  [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 5, 4, 6, 7 ], [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 5, 4, 6 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 12, 11, 14, 15 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 4, 13, 10, 12, 11 ], [ 1, 3, 2, 4 ], [ 1, 3, 2, 4 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 12, 11, 14, 15 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 4, 13, 10, 12, 11 ],
  [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 11, 12, 14, 15 ], [ 1, 5, 3, 6, 2, 7, 8, 10, 9, 11, 4, 17, 12, 13, 15, 14, 16 ], [ 1, 5, 3, 6, 2, 7, 8, 9, 10, 4, 15, 11, 12, 13, 14 ],
  [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ], [ 1, 3, 2, 4 ], [ 1, 3, 2, 5, 4, 6, 7 ], [ 1, 5, 3, 6, 2, 7, 8, 4, 9, 12, 10, 11 ],
  [ 1, 3, 2, 4 ], [ 1, 3, 2, 4 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 4, 10, 13, 16, 12, 11, 14, 15 ], [ 1, 5, 3, 6, 7, 2, 8, 9, 10, 4, 11, 16, 17, 21, 12, 14, 13, 15, 18, 19, 20 ],
  [ 1, 3, 2, 4 ] ];;
testtranslation:=function()
  local groups, sglids, n;
    groups := List([1..69], i->List(idstodo[i], x->AllSOTGroups(ordstodo[i])[x]));;
    sglids := List([1..69], i->List(groups[i], x->IdGroup(x)[2]));;
    return sglids = List([1..69], i->[1..NumberOfSOTGroups(ordstodo[i])]);
  end;
