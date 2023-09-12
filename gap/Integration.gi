## Integration with SmallGrps


# Get the next available "layer" id (the built-in library
# consists of 11 layers, but other packages may already have
# added further layers).
BindGlobal("SOTGRPS_LAYER", Length(SMALL_AVAILABLE_FUNCS) + 1);

# Determine where to add our new lookup functions
BindGlobal("SOTGRPS_POS", Maximum(List([
        SMALL_GROUP_FUNCS,
        SMALL_GROUPS_INFORMATION,
        NUMBER_SMALL_GROUPS_FUNCS,
        ID_GROUP_FUNCS,
        SELECT_SMALL_GROUPS_FUNCS,
    ], Length)) + 1);

#
# hook us up on the layer level
#

# meta data on small groups data we provide
SMALL_AVAILABLE_FUNCS[SOTGRPS_LAYER] := function( size )
    if IsSOTAvailable(size) then
        return rec (
            lib := SOTGRPS_LAYER,
            func := SOTGRPS_POS,
            number := NumberOfSOTGroups(size)    # number of groups of this order
        );
    fi;
    return fail;
end;

# meta data on IdGroup functionality we provide
ID_AVAILABLE_FUNCS[SOTGRPS_LAYER] := SMALL_AVAILABLE_FUNCS[SOTGRPS_LAYER];

# Method for SmallGroup(size, i):
SMALL_GROUP_FUNCS[ SOTGRPS_POS ] := function( size, i, inforec )
    local g;

    # Now create the actual group
    g := SOTGroup(size, i);

    return g;
end;

# Method which selects a subset of all those groups with
# a certain combination of properties.
# A default method can be used; but more user friendly would be
# to install something custom which e.g. takes care of filtering
# the abelian /nilpotent / solvable groups.
SELECT_SMALL_GROUPS_FUNCS[ SOTGRPS_POS ] := SELECT_SMALL_GROUPS_FUNCS[ 11 ];
#SELECT_SMALL_GROUPS_FUNCS[ pos ] := function( funcs, vals, inforec, all, id )
#    Error("TODO");
#end;

# Method for IdGroup(size, i).
ID_GROUP_FUNCS[ SOTGRPS_POS ] := function( G, inforec )
    return IdSOTGroup(G)[2];
end;

# Method for SmallGroupsInformation(size):
SMALL_GROUPS_INFORMATION[ SOTGRPS_POS ] := function( size, inforec, num )
    local fac, ind;
    fac := Collected(Factors(size));
    SortBy(fac, Reversed);
    ind := List(fac, x -> x[2]);
    _SOTGroupsInformation(size, fac, ind);
    Print("\n");
end;
