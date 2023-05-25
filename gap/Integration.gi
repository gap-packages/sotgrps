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
    if IsSOTAvailable(size) then
        return rec (
            lib := layer,
            func := pos,
            number := NumberOfSOTGroups(size)    # number of groups of this order
        );
    fi;
end;

# meta data on IdGroup functionality we provide
ID_AVAILABLE_FUNCS[layer] := function( size )
    # Three possible implementations:

    # 1. No IdGroup functionality at all:

    # 2. IdGroup provided for all groups:
    return SMALL_AVAILABLE_FUNCS[layer];

    # 3. IdGroup provided for a subset of order
    #if size in [ 12345, 67890 ] then
    #  return SMALL_AVAILABLE_FUNCS[layer];
    #fi;

end;

# Method for SmallGroup(size, i):
SMALL_GROUP_FUNCS[ pos ] := function( size, i, inforec )
    local g;

    # Now create the actual group
    g := SOTGroup(size, i);

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
    return IdSOTGroup(G);
end;

# Method for SmallGroupsInformation(size):
SMALL_GROUPS_INFORMATION[ pos ] := function( size, inforec, num )
    #Print( " \n");
    #Print( "      This database was created by BLA, see paper BLUB.\n");
    SOTGroupsInformation(size);
    return;
end;
