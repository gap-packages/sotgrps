##In the following we give the main functions of the SOTGrps package.
############################################################################
##AllSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs all the isomorohism types of groups of order n.
##If the group is solvable, then it is presented as a PcGroup.
InstallGlobalFunction( AllSOTGroups, function(n, arg...)
	local fac, ind, grps, i;
		SOTRec.PCP := Length(arg) > 0 and arg[1] = IsPcpGroup;
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
			grps := SOTRec.allGroupsP2QR(n);
		elif ind = [1, 1, 1, 1] then
			grps := SOTRec.allGroupsPQRS(n);
		elif ind = [1, 4] then
			grps := SOTRec.allGroupsP4Q(fac[2][1], fac[1][1]);
		else
			Error("Order ", n, " is not supported by SOTGrps; please refer to the documentation for AllSOTGroups for the list of supported orders.\n");
		fi;

        for i in [1..Length(grps)] do
            SetIdSOTGroup(grps[i], [n, i]);
        od;
        return grps;
end);
############################################################################
##NumberOfSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs the number of isomorphism types of groups of order n.
	##For orders that factorise in at most four primes, see [2, Theorem 2.1] for further details.
InstallGlobalFunction( NumberOfSOTGroups, function(n)
	local fac, ind;
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
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
			return SOTRec.NumberGroupsP2QR(n);
		elif ind = [1, 1, 1, 1] then
			return SOTRec.NumberGroupsPQRS(n);
		elif ind = [1, 4] then
			return SOTRec.NumberGroupsP4Q(fac[2][1], fac[1][1]);
		else
			Error("Order ", n, " is not supported by SOTGrps; please refer to the documentation of function NumberOfSOTGroups for the list of suppoorted orders.\n");
		fi;
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
	local fac, ind, G;
		SOTRec.PCP := Length(arg) > 0 and arg[1] = IsPcpGroup;
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
		if i <= NumberOfSOTGroups(n) then
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
				G := SOTRec.GroupP2QR(n, i);
			elif ind = [1, 1, 1, 1] then
				G := SOTRec.GroupPQRS(n, i);
			elif ind = [1, 4] then
				G := SOTRec.GroupP4Q(fac[2][1], fac[1][1], i);
			else
				Error("Order ", n, " is not supported by SOTGrps; please refer to the documentation of function SOTGroup for the list of suppoorted orders.\n");
			fi;
			SetIdSOTGroup(G, [n, i]);
			return G;
		fi;

		Error("Wrong input: there are in total ", NumberOfSOTGroups(n), " groups of order ", n, ".\n");
end);
############################################################################
##SOTGroupsInformation(n) gives the enumeration of groups of order n if IsSOTAvailable(n) = true.
InstallGlobalFunction( SOTGroupsInformation, function(n)
	local fac, ind;
			fac := Collected(Factors(n));
			SortBy(fac, Reversed);
			ind := List(fac, x -> x[2]);
			if Length(ind) = 1 then ##p-groups
				if ind = [1] then Print("There is a unique group of order", n, "up to isomorphism, and it is cyclic.");
				elif ind = [2] then Print("There are two isomorphism types of p-groups of order ", n, ": there is one cyclic group, and one elementary abelian group.");
				elif ind = [3] then Print("There are five isomorpshim types of p-groups of order ", n, ": there are three abelian groups, and two extraspecial groups.");
				elif ind = [4] then
					if fac[1] = 2 then Print("There are 14 isomorphism types of p-groups of order 16: there are 5 abelian groups, and 9 nonabelian groups.");
					else Print("There are 15 isomorphism types of groups of order ", n, ": there are 5 abelian groups, and 10 nonabelian groups.");
					fi;
				fi;
			elif ind = [1, 1] then ##pq, a = 1
				if (fac[2][1] - 1) mod fac[1][1] = 0 then
					Print("There are two isomorphism types of squarefree groups of order ", n, ": there is one abelian group, and one nonebalian group.");
				else Print("There is a unique group of order ", n, ", up to isomorphism, and it is abelian.");
				fi;
			elif ind = [1, 2] then
				if not (fac[1][1] - 1) mod fac[2][1] = 0 and not (fac[2][1] - 1) mod fac[1][1] = 0 then
					Print("There are two isomorphism types of order ", n, ": one is cyclic, and one is isomorphic to the abelian group(", [n, 2], ").");
				else Print("There are ", SOTRec.NumberGroupsP2Q(fac[2][1], fac[1][1]), " isomorphism types of groups of order ", n, ".");
				fi;
			elif ind = [1, 1, 1] then
				Print("There are ", SOTRec.NumberGroupsPQR(n), " isomorphism types of squarefree groups of order ", n, ".");
			elif ind = [2, 2] then
				SOTRec.infoP2Q2(n);
			elif ind = [1, 3] then
				SOTRec.infoP3Q(n);
			elif ind = [1, 1, 2] then
				SOTRec.infoP2QR(n);
			elif ind = [1, 1, 1, 1] then
				SOTRec.infoPQRS(n);
			elif ind = [1, 4] then
				SOTRec.infoP4Q(n);
			elif Sum(ind) >= 5 then
				Error("Order ", n, " is not supported by SOTGrps; please refer to the documentation for SOTGroupsInformation for the list of supported groups.");
			fi;
end);

######################################################
##IdSOTGroup takes in a group G (that is, IsGroup(G) = true) of order n such that IsSOTAvailable(n) = true and determines its SOT-group ID.
	##That is, it outputs an ordered pair (n, i) where m = |G| and i is the position of G in the list AllSOTGroups(n).
InstallMethod( IdSOTGroup, [ IsGroup ],
function(group)
	local n, ind, fac;
		if not IsFinite(group) then
			TryNextMethod();
		fi;
		n := Size(group);
		fac := Collected(Factors(n));
		SortBy(fac, Reversed);
		ind := List(fac, x -> x[2]);
		if ind in [ [1], [2], [3], [4] ] then
			return SOTRec.IdPGroup(group);
		elif ind = [1, 1] then
			return SOTRec.IdGroupPQ(group);
		elif ind = [1, 2] then
			return SOTRec.IdGroupP2Q(group);
		elif ind = [1, 1, 1] then
			return SOTRec.IdGroupPQR(group);
		elif ind = [2, 2] then
			return SOTRec.IdGroupP2Q2(group);
		elif ind = [1, 3] then
			return SOTRec.IdGroupP3Q(group);
		elif ind = [1, 1, 2] then
			return SOTRec.IdGroupP2QR(group);
		elif ind = [1, 1, 1, 1] then
			return SOTRec.IdGroupPQRS(group);
		elif ind = [1, 4] then
			return SOTRec.IdGroupP4Q(group);
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
