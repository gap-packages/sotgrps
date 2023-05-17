##In the following we give the main functions of the SOTGrps package.
############################################################################
##AllSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs all the isomorohism types of groups of order n.
	##If the group is solvable, then it is presented as a PcGroup; set USE_PCP := true if PcpGroup is desired.
InstallGlobalFunction( AllSOTGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(PF);
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return SOTRec.lowpowerPGroups(p, k);
		fi;

		if List(fac, x -> x[2]) = [1, 1] then
			return SOTRec.allGroupsPQ(n);
		elif length = 3 and Length(fac) = 2 then
			return SOTRec.allGroupsP2Q(n);
		elif List(fac, x -> x[2]) = [1, 1, 1] then
			return SOTRec.allGroupsPQR(n);
		elif List(fac, x -> x[2]) = [2, 2] then
			return SOTRec.allGroupsP2Q2(n);
		elif length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return SOTRec.allGroupsP3Q(n);
		elif length = 4 and Length(fac) = 3 then
			return SOTRec.allGroupsP2QR(n);
		elif List(fac, x -> x[2]) = [1, 1, 1, 1] then
			## To use the construction by case distinction on the size of F (the Fitting subgroup of G), set USE_pqrsII := false; otherwise, the main construction functions AllSOTGroups and SOTGroup use the case distinction by the centre and the derived subgroup of G, with USE_pqrsII = true.
			if USE_pqrsII = true then
				return SOTRec.allGroupsPQRSII(n);
			else return SOTRec.allGroupsPQRS(n);
			fi;
		elif length = 5 and List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then
			return SOTRec.allGroupsP4Q(n);
		else
			Error("Groups of order ", n, " are not available: AllSOTGroups(#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes or # = p^4q for distinct primes p and q.");
		fi;
end);
############################################################################
##NumberOfSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs the number of isomorphism types of groups of order n.
	##For orders that factorise in at most four primes, see [2, Theorem 2.1] for further details.
InstallGlobalFunction( NumberOfSOTGroups, function(n)
	local fac, ind;
		fac := Collected(Factors(n));
		ind := List(fac, x -> x[2]);
		if ind in [ [1], [2], [3], [4] ] then
				return SOTRec.NumberPGroups(n);
		elif ind = [1, 1] then
			return SOTRec.NumberGroupsPQ(n);
		elif ind in [ [1, 2], [2, 1] ] then
			return SOTRec.NumberGroupsP2Q(n);
		elif ind = [1, 1, 1] then
			return SOTRec.NumberGroupsPQR(n);
		elif ind = [2, 2] then
			return SOTRec.NumberGroupsP2Q2(n);
		elif ind in [ [1, 3], [3, 1] ] then
			return SOTRec.NumberGroupsP3Q(n);
		elif ind in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ] then
			return SOTRec.NumberGroupsP2QR(n);
		elif ind = [1, 1, 1, 1] then
			return SOTRec.NumberGroupsPQRS(n);
		elif ind in [ [1, 4], [4, 1] ] then
			return SOTRec.NumberGroupsP4Q(n);
		else
			Error("Order ", n, " is not available: NumberOfSOTGroups(#) returns the number of isomorphism types of groups of order that factorises into at most 4 primes or of the form p^4q.");
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
InstallGlobalFunction( SOTGroup, function(n, i)
	local fac, ind, p, k, G;
		fac := Collected(Factors(n));
		ind := List(fac, x -> x[2]);
		if i <= NumberOfSOTGroups(n) then
			if ind in [ [1], [2], [3], [4] ] then
				p := fac[1][1];
				k := fac[1][2];
				return SOTRec.PGroup(p, k, i);
			elif ind = [1, 1] then
				G := SOTRec.GroupPQ(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif ind in [ [1, 2], [2, 1] ] then
				G := SOTRec.GroupP2Q(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif ind = [1, 1, 1] then
				G := SOTRec.GroupPQR(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif ind = [2, 2] then
				G := SOTRec.GroupP2Q2(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif ind in [ [1, 3], [3, 1] ] then
				G := SOTRec.GroupP3Q(n, i);
				SetSOTGroup_id(G, [n, i]);
				return G;
			elif ind in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ] then
				return SOTRec.GroupP2QR(n, i);
			elif ind = [1, 1, 1, 1] then
				if USE_pqrsII = true then
					G := SOTRec.GroupPQRSII(n, i);
				else
					G := SOTRec.GroupPQRS(n, i);
				fi;
				SetSOTGroup_id(G, [n, i]);
				return G;
			elif ind in [ [1, 4], [4, 1] ] then
				return SOTRec.GroupP4Q(n, i);
			else
				Error("Groups of order ", n, " are not available in sotgrps.");
			fi;
		fi;

		if i > NumberOfSOTGroups(n) then
			Error("Wrong input: there are in total ", NumberOfSOTGroups(n), " groups of order ", n, ".");
		fi;

end);
############################################################################
##SOTGroupsInformation() introduces the main function AllSOTGroups.
##SOTGroupsInformation(n) gives the enumeration of groups of order n if IsSOTAvailable(n) = true.
InstallGlobalFunction( SOTGroupsInformation, function(arg)
	local fac, ind, n;
		if Length(arg) = 0 then
			Print("AllSOTGroups(#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes or # = p^4q, where p and q are distinct primes.");
		fi;
		if Length(arg) = 1 then
			n := arg[1];
			fac := Collected(Factors(n));
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
  		fi;

  		if ind = [1, 1] then ##pq, a = 1
  			if (fac[2][1] - 1) mod fac[1][1] = 0 then
  				Print("There are two isomorphism types of squarefree groups of order ", n, ": there is one abelian group, and one nonebalian group.");
  			else Print("There is a unique group of order ", n, ", up to isomorphism, and it is abelian.");
  			fi;
  		elif ind in [ [1, 2], [2, 1] ] then
  			if not (fac[1][1] - 1) mod fac[2][1] = 0 and not (fac[2][1] - 1) mod fac[1][1] = 0 then
  				Print("There are two isomorphism types of order ", n, ": one is cyclic, and one is isomorphic to the abelian group(", [n, 2], ").");
  			else Print("There are ", SOTRec.NumberGroupsP2Q(n), " isomorphism types of groups of order ", n, ".");
  			fi;
  		elif ind = [1, 1, 1] then
  			Print("There are ", SOTRec.NumberGroupsPQR(n), " isomorphism types of squarefree groups of order ", n, ".");
  		elif ind = [2, 2] then
  			Print("There are ", SOTRec.NumberGroupsP2Q2(n), " isomorphism types of groups of order ", n, ".");
  		elif ind in [ [1, 3], [3, 1] ] then
				SOTRec.infoP3Q(n);
  		elif ind in [ [1, 1, 2], [1, 2, 1], [2, 1, 1] ] then
				SOTRec.infoP2QR(n);
  		elif ind = [1, 1, 1, 1] then
				SOTRec.infoPQRS(n);
  		elif ind in [ [1, 4], [4, 1] ] then
				Print("There are ", SOTRec.NumberGroupsPQRS(n), " isomorphism types of groups of order ", n, ".");
			elif Sum(ind) >= 5 then
				Error("Order ", n, " is not available in sotgrps.");
			fi;

    elif Length(arg) > 1 then Error("Too many arguments: number of arguments must be 0 or 1.");
    fi;
end);

######################################################
##IdSOTGroup takes in a group G (that is, IsGroup(G) = true) of order n such that IsSOTAvailable(n) = true and determines its SOT-group ID.
	##That is, it outputs an ordered pair (n, i) where m = |G| and i is the position of G in the list AllSOTGroups(n).
InstallGlobalFunction( IdSOTGroup, function(group)
	local n, ind, fac;
		if HasSOTGroup_id(group) then
			return SOTGroup_id(group);
		fi;
		n := Size(group);
		fac := Collected(Factors(n));
		ind := List(fac, x -> x[2]);
		if ind in [ [1], [2], [3], [4] ] then
			return SOTRec.IdPGroup(group);
		elif ind = [1, 1] then
			return SOTRec.IdGroupPQ(group);
		elif ind in [ [1, 2], [2, 1] ] then
			return SOTRec.IdGroupP2Q(group);
		elif ind = [1, 1, 1] then
			return SOTRec.IdGroupPQR(group);
		elif ind = [2, 2] then
			return SOTRec.IdGroupP2Q2(group);
		elif ind in [ [1, 3], [3, 1] ] then
			return SOTRec.IdGroupP3Q(group);
		elif ind in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ] then
			return SOTRec.IdGroupP2QR(group);
		elif ind = [1, 1, 1, 1] then
			if USE_pqrsII = true then
				return SOTRec.IdGroupPQRSII(group);
			else
				return SOTRec.IdGroupPQRS(group);
			fi;
		elif ind in [ [1, 4], [4, 1]] then
			return SOTRec.IdGroupP4Q(group);
		else
			Error("Groups of order ", n, " is not available in sotgrps: IdSOTGroup (#) determines groups of order # up to isomorphism, where # factorises into at most 4 primes or is of the form p^4q, where p, q are distinct primes.");
		fi;
end);

######################################################
## IsIsomorphicSOTGroups takes in two groups G and H, whose orders are available in sotgrps
## and determines whether G is isomprphic to H.
InstallGlobalFunction( IsIsomorphicSOTGroups, function(G, H)
	return Size(G) = Size(H) and IdSOTGroup(G) = IdSOTGroup(H);
end);
