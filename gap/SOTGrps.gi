BindGlobal("_SOT_UnsupportedOrder", function(n)
    Error("Order ", n, " is not supported by SOTGrps.\n",
          "Please refer to the SOTGrps documentation for the list of supported orders.");
end);

##In the following we give the main functions of the SOTGrps package.
############################################################################
##AllSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs all the isomorohism types of groups of order n.
##If the group is solvable, then it is presented as a PcGroup.
InstallGlobalFunction( AllSOTGroups, function(n, arg...)
	local fac, ind, grps, i;
		SOTRec.PCP := Length(arg) > 0 and IsBoundGlobal("IsPcpGroup") and arg[1] = ValueGlobal("IsPcpGroup");
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
		if Length(fac) = 1 then
			grps := SOTRec.lowpowerPGroups(fac[1][1], fac[1][2]);
		elif ind = [1, 1] then
			grps := SOTRec.allGroupsPQ(fac[2][1], fac[1][1]);
		elif ind = [1, 2] then
			grps := SOTRec.allGroupsP2Q(fac[2][1], fac[1][1]);
		elif ind = [1, 1, 1] then
			grps := SOTRec.allGroupsPQR(fac[3][1], fac[2][1], fac[1][1]);
		elif ind = [2, 2] then
			grps := SOTRec.allGroupsP2Q2(fac[2][1], fac[1][1]);
		elif ind = [1, 3] then
			grps := SOTRec.allGroupsP3Q(fac[2][1], fac[1][1]);
		elif ind = [1, 1, 2] then
			grps := SOTRec.allGroupsP2QR(fac[3][1], fac[1][1], fac[2][1]);
		elif ind = [1, 1, 1, 1] then
			grps := SOTRec.allGroupsPQRS(fac[1][1], fac[2][1], fac[3][1], fac[4][1]);
		elif ind = [1, 4] then
			grps := SOTRec.allGroupsP4Q(fac[2][1], fac[1][1]);
		else
			_SOT_UnsupportedOrder(n);
		fi;

        for i in [1..Length(grps)] do
            SetIdSOTGroup(grps[i], [n, i]);
        od;
        return grps;
end);
############################################################################
##NumberOfSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs the number of isomorphism types of groups of order n.
	##For orders that factorise in at most four primes, see [2, Theorem 2.1] for further details.
BindGlobal( "_NumberOfSOTGroups", function(n, fac, ind)
		if ind in [ [1], [2], [3], [4] ] then
			return SOTRec.NumberPGroups(fac[1][1], fac[1][2]);
		elif ind = [1, 1] then
			return SOTRec.NumberGroupsPQ(fac[2][1], fac[1][1]);
		elif ind = [1, 2] then
			return SOTRec.NumberGroupsP2Q(fac[2][1], fac[1][1]);
		elif ind = [1, 1, 1] then
			return SOTRec.NumberGroupsPQR(fac[3][1], fac[2][1], fac[1][1]);
		elif ind = [2, 2] then
			return SOTRec.NumberGroupsP2Q2(fac[2][1], fac[1][1]);
		elif ind = [1, 3] then
			return SOTRec.NumberGroupsP3Q(fac[2][1], fac[1][1]);
		elif ind = [1, 1, 2] then
			return SOTRec.NumberGroupsP2QR(fac[3][1], fac[1][1], fac[2][1]);
		elif ind = [1, 1, 1, 1] then
			return SOTRec.NumberGroupsPQRS(fac[1][1], fac[2][1], fac[3][1], fac[4][1]);
		elif ind = [1, 4] then
			return SOTRec.NumberGroupsP4Q(fac[2][1], fac[1][1]);
		else
			_SOT_UnsupportedOrder(n);
		fi;
	end);

InstallGlobalFunction( NumberOfSOTGroups, function(n)
    local fac, ind;
    fac := Collected(Factors(n));
    SortBy(fac, Reversed);
    ind := List(fac, x -> x[2]);
    return _NumberOfSOTGroups(n, fac, ind);
end);

############################################################################
##IsSOTAvailable takes in a positive integer value n, and determines whether the groups of order n are available in the SOTGrps package.
InstallGlobalFunction( IsSOTAvailable, function(n)
	local PF;
		PF := Factors(n);
		if Length(PF) <= 4 then
			return true;
		fi;
		if List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then
			return true;
		fi;
		return false;
end);
############################################################################
##SOTGroup takes in an ordered pair of positive integers (n, i), it outputs the i-th groups in the list AllSOTGroups(n). That is, it outputs the i-th isomorphism type of groups of order n.
InstallGlobalFunction( SOTGroup, function(n, i, arg...)
	local fac, ind, G, num;
		SOTRec.PCP := Length(arg) > 0 and IsBoundGlobal("IsPcpGroup") and arg[1] = ValueGlobal("IsPcpGroup");
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
		num := _NumberOfSOTGroups(n, fac, ind);
		if i <= num then
			if ind in [ [1], [2], [3], [4] ] then
				G := SOTRec.PGroup(fac[1][1], fac[1][2], i);
			elif ind = [1, 1] then
				G := SOTRec.GroupPQ(fac[2][1], fac[1][1], i);
			elif ind = [1, 2] then
				G := SOTRec.GroupP2Q(fac[2][1], fac[1][1], i);
			elif ind = [1, 1, 1] then
				G := SOTRec.GroupPQR(fac[3][1], fac[2][1], fac[1][1], i);
			elif ind = [2, 2] then
				G := SOTRec.GroupP2Q2(fac[2][1], fac[1][1], i);
			elif ind = [1, 3] then
				G := SOTRec.GroupP3Q(fac[2][1], fac[1][1], i);
			elif ind = [1, 1, 2] then
				G := SOTRec.GroupP2QR(fac[3][1], fac[1][1], fac[2][1], i);
			elif ind = [1, 1, 1, 1] then
				G := SOTRec.GroupPQRS(fac[1][1], fac[2][1], fac[3][1], fac[4][1], i);
			elif ind = [1, 4] then
				G := SOTRec.GroupP4Q(fac[2][1], fac[1][1], i);
			else
				_SOT_UnsupportedOrder(n);
			fi;
			SetIdSOTGroup(G, [n, i]);
			return G;
		fi;

		Error("Wrong input: there are in total ", num, " groups of order ", n, ".");
end);
############################################################################
##SOTGroupsInformation(n) gives the enumeration of groups of order n if IsSOTAvailable(n) = true.
BindGlobal( "_SOTGroupsInformation", function(n, fac, ind)
    Print("\>\>\n");
    if ind = [1] then
        Print("There is 1 cyclic group.");
    elif ind = [2] then
        Print("There is 1 cyclic group, and 1 elementary abelian group.");
    elif ind = [3] then
        Print("There are 3 abelian groups, and 2 extraspecial groups.");
    elif ind = [4] then
        if fac[1] = 2 then
            Print("There are 5 abelian groups, and 9 nonabelian groups.");
        else
            Print("There are 5 abelian groups, and 10 nonabelian groups.");
        fi;
    elif ind = [1, 1] then ##pq, a = 1
        if (fac[2][1] - 1) mod fac[1][1] = 0 then
            Print("There is 1 cyclic group, and 1 nonabelian group.");
        else
            Print("There is 1 cyclic group.");
        fi;
    elif ind = [1, 2] then
        if not (fac[1][1] - 1) mod fac[2][1] = 0 and
           not (fac[2][1] - 1) mod fac[1][1] = 0 then
            Print("There are 2 abelian groups.");
        else
            Print("There are 2 abelian groups, the rest is non-abelian.");
        fi;
    elif ind = [1, 1, 1] then
        Print("The order is square free.");
    elif ind = [2, 2] then
        SOTRec.infoP2Q2(n, fac);
    elif ind = [1, 3] then
        SOTRec.infoP3Q(n, fac);
    elif ind = [1, 1, 2] then
        SOTRec.infoP2QR(n, fac);
    elif ind = [1, 1, 1, 1] then
        SOTRec.infoPQRS(n, fac);
    elif ind = [1, 4] then
        SOTRec.infoP4Q(n, fac);
    else
        _SOT_UnsupportedOrder(n);
    fi;
    Print("\<\<");
end);

InstallGlobalFunction( SOTGroupsInformation, function(n)
    local fac, ind, num;
    fac := Collected(Factors(n));
    SortBy(fac, Reversed);
    ind := List(fac, x -> x[2]);

    num := _NumberOfSOTGroups(n, fac, ind);
    if num = 1 then
        Print("\n  There is 1 group of order ",n,".\n");
    else
        Print("\n  There are ",num," groups of order ",n,".\n" );
    fi;
    _SOTGroupsInformation(n, fac, ind);
    Print("\n");
end);

######################################################
##IdSOTGroup takes in a group G (that is, IsGroup(G) = true) of order n such that IsSOTAvailable(n) = true and determines its SOT-group ID.
	##That is, it outputs an ordered pair (n, i) where m = |G| and i is the position of G in the list AllSOTGroups(n).
InstallMethod( IdSOTGroup, [ IsGroup and IsFinite ],
function(group)
	local n, ind, fac;
		n := Size(group);
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
		if ind in [ [1], [2], [3], [4] ] then
			return SOTRec.IdPGroup(group, n, fac);
		elif ind = [1, 1] then
			return SOTRec.IdGroupPQ(group, n, fac);
		elif ind = [1, 2] then
			return SOTRec.IdGroupP2Q(group, n, fac);
		elif ind = [1, 1, 1] then
			return SOTRec.IdGroupPQR(group, n, fac);
		elif ind = [2, 2] then
			return SOTRec.IdGroupP2Q2(group, n, fac);
		elif ind = [1, 3] then
			return SOTRec.IdGroupP3Q(group, n, fac);
		elif ind = [1, 1, 2] then
			return SOTRec.IdGroupP2QR(group, n, fac);
		elif ind = [1, 1, 1, 1] then
			return SOTRec.IdGroupPQRS(group, n, fac);
		elif ind = [1, 4] then
			return SOTRec.IdGroupP4Q(group, n, fac);
		else
			Error("Groups of order ", n, " are not supported by SOTGrps; please refer to the documentation for IdSOTGroup for the list of supported groups.");
		fi;
end);

######################################################
## IsIsomorphicSOTGroups takes in two groups G and H, whose orders are available in sotgrps
## and determines whether G is isomprphic to H.
InstallGlobalFunction( IsIsomorphicSOTGroups, function(G, H)
	return Size(G) = Size(H) and IdSOTGroup(G) = IdSOTGroup(H);
end);
