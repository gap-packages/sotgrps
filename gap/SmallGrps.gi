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
			return msg.lowpowerPGroups(p, k);
		fi;

		if List(fac, x -> x[2]) = [1, 1] then
			return msg.allGroupsPQ(n);
		elif length = 3 and Length(fac) = 2 then
			return msg.allGroupsP2Q(n);
		elif List(fac, x -> x[2]) = [1, 1, 1] then
			return msg.allGroupsPQR(n);
		elif List(fac, x -> x[2]) = [2, 2] then
			return msg.allGroupsP2Q2(n);
		elif length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return msg.allGroupsP3Q(n);
		elif length = 4 and Length(fac) = 3 then
			return msg.allGroupsP2QR(n);
		elif List(fac, x -> x[2]) = [1, 1, 1, 1] then
			## To use the construction by case distinction on the size of F (the Fitting subgroup of G), set USE_pqrsII := false; otherwise, the main construction functions AllSOTGroups and SOTGroup use the case distinction by the centre and the derived subgroup of G, with USE_pqrsII = true.
			if USE_pqrsII = true then
				return msg.allGroupsPQRSII(n);
			else return msg.allGroupsPQRS(n);
			fi;
		elif length = 5 and List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then
			return msg.allGroupsP4Q(n);
		else
			Print(("Groups of order "), n, (" is not available in mysmallgrps: AllSOTGroups (#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes or # = p^4q for distinct primes p and q."));
		fi;
end);
############################################################################
##NumberOfSOTGroups takes in a positive integer n that factorise in at most 4 primes or has the form p^4q (p, q are distinct primes), and outputs the number of isomorphism types of groups of order n.
	##For orders that factorise in at most four primes, see [2, Theorem 2.1] for further details.
InstallGlobalFunction( NumberOfSOTGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(PF);
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			if length < 5 then
				return msg.NumberPGroups(n);
			fi;
		fi;

		if List(fac, x -> x[2]) = [1, 1] then
			return msg.NumberGroupsPQ(n);
		elif length = 3 and Length(fac) = 2 then
			return msg.NumberGroupsP2Q(n);
		elif length = 3 and Length(fac) = 3 then
			return msg.NumberGroupsPQR(n);
		elif length = 4 and List(Collected(PF), x -> x[2]) = [2, 2] then
			return msg.NumberGroupsP2Q2(n);
		elif length = 4 and List(Collected(PF), x -> x[2]) in [ [1, 3], [3, 1] ] then
			return msg.NumberGroupsP3Q(n);
		elif length = 4 and Length(fac) = 3 then
			return msg.NumberGroupsP2QR(n);
		elif length = 4 and Length(fac) = 4 then
			return msg.NumberGroupsPQRS(n);
		elif length = 5 and List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then
			return msg.NumberGroupsP4Q(n);
		else
			Print(("Order "), n, (" is not available in mysmallgrps: NumberOfSOTGroups(#) returns the number of isomorphism types of groups of order that factorises into at most 4 primes or of the form p^4q."));
		fi;
	end);

############################################################################
##SOTGroupIsAvailable takes in a positive integer value n, and determines whether the groups of order n are available in the SOTGrps package.
InstallGlobalFunction( SOTGroupIsAvailable, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if length > 4 and not List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then return false; fi;
		return true;
end);
############################################################################
##SOTGroup takes in an ordered pair of positive integers (n, i), it outputs the i-th groups in the list AllSOTGroups(n). That is, it outputs the i-th isomorphism type of groups of order n.
InstallGlobalFunction( SOTGroup, function(n, i)
	local length, PF, fac, k, p, q, r, G;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(PF);
		if i < (NumberOfSOTGroups(n) + 1) then
			if Length(fac) = 1 then
				p := PF[1];
				k := length;
				return msg.PGroup(p, k, i);
			elif length = 2 and Length(fac) = 2 then
				G := msg.GroupPQ(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif length = 3 and Length(fac) = 2 then
				G := msg.GroupP2Q(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif length = 3 and Length(fac) = 3 then
				G := msg.GroupPQR(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
				G := msg.GroupP2Q2(n, i);
				SetSOTGroup_id(G,[n,i]);
				return G;
			elif length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
				G := msg.GroupP3Q(n, i);
				SetSOTGroup_id(G, [n, i]);
				return G;
			elif length = 4 and Length(fac) = 3 then
				return msg.GroupP2QR(n, i);
			elif length = 4 and Length(fac) = 4 then
				if USE_pqrsII = true then
					G := msg.GroupPQRSII(n, i);
				else
					G := msg.GroupPQRS(n, i);
				fi;
				SetSOTGroup_id(G, [n, i]);
				return G;
			elif length = 5 and List(Collected(PF), x -> x[2]) in [ [1, 4], [4, 1] ] then
				return msg.GroupP4Q(n, i);
			else
				Print(("Groups of order "), n, (" is not available in mysmallgrps."));
			fi;
		fi;

		if Length(fac) > 1 and i > NumberOfSOTGroups(n) then
			Print(("Wrong input: there are in total "), NumberOfSOTGroups(n), (" isomorphism types of groups of order "), n, ("."));
		fi;

end);
############################################################################
##SOTGroupsInformation() introduces the main function AllSOTGroups.
##SOTGroupsInformation(n) gives the enumeration of groups of order n if SOTGroupIsAvailable(n) = true.
InstallGlobalFunction( SOTGroupsInformation, function(arg)
	local length, PF, fac, n, k, p, q, r;
		if Length(arg) = 0 then
			Print("AllSOTGroups(#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes or # = p^4q, where p and q are distinct primes.");
    fi; # FIXME: this code is mixing tabs and spaces, which makes it weird to read unless one has the exact same tab settings as your computer.
    # In general we recommend using only spaces, not tabs, to avoid this. It is possible to fix this with a script, let me know if you are interested in help with that
		if Length(arg) = 1 then
			n := arg[1];
      PF := Factors(n);
  		length := Length(PF);
  		fac := Collected(PF);

  		if Length(fac) = 1 then ##p-groups
  			p := PF[1];
  			k := length;
  			if k = 1 then Print(("There is a unique group of order"), n, ("up to isomorphism, and it is cyclic.") );
  			# FIXME: the parenthesis around the strings are superfluous
  			elif k = 2 then Print(("There are two isomorphism types of p-groups of order "),n,(": there is one cyclic group, and one elementary abelian group."));
  			elif k = 3 then Print(("There are five isomorpshim types of p-groups of order "), n, (": there are 3 abelian groups, and 3 extraspecial groups."));
  			elif k = 4 then
  				if p = 2 then Print("There are 14 isomorphism types of p-groups of order 16: there are 5 abelian groups, and 9 nonabelian groups.");
  				else Print(("There are 15 isomorphism types of groups of order "), n, (": there are 5 abelian groups, and 10 nonabelian groups."));
  				fi;
  			fi;
  		fi;

  		if length = 2 and Length(fac) = 2 then ##p^aq, a = 1
  			if (PF[2] - 1) mod PF[1] = 0 then
  				Print(("There are two isomorphism types of squarefree groups of order "), n, (": there is one abelian group, and one nonebalian group."));
  			else Print(("There is a unique group of order "), n, (", up to isomorphism, and it is abelian."));
  			fi;
  		elif length = 3 and Length(fac) = 2 then
  			if not (PF[1] - 1) mod PF[3] = 0 and not (PF[3] - 1) mod PF[1] = 0 then
  				Print(("There are two isomorphism types of order "), n, (": one is cyclic, and one is isomorphic to AbelianGroup("), p*q, p, (")."));
  			else Print(("There are "), msg.NumberGroupsP2Q(n), (" isomorphism types of groups of order "), n, ("."));
  			fi;
  		elif length = 3 and Length(fac) = 3 then
  			Print(("There are "), msg.NumberGroupsPQR(n), (" isomorphism types of squarefree groups of order "), n, ("."));
  		elif length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
  			Print(("There are "), msg.NumberGroupsP2Q2(n), (" isomorphism types of groups of order "), n, ("."));
  		elif length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
  			Print(("There are "), msg.NumberGroupsP3Q(n), (" isomorphism types of groups of order "), n, ("."));
  		elif length = 4 and Length(fac) = 3 then
  			Print(("There are "), msg.NumberGroupsP2QR(n), (" isomorphism types of groups of order "), n, ("."));
  		elif length = 4 and Length(fac) = 4 then
				Print(("There are "), msg.NumberGroupsPQRS(n), (" isomorphism types of groups of order "), n, ("."));
  		elif length = 5 and List(fac, x -> x[2]) in [ [1, 4], [4, 1] ] then
				Print(("There are "), msg.NumberGroupsPQRS(n), (" isomorphism types of groups of order "), n, ("."));
			elif length > 5 then
				Print(("Order "), n, (" is not available in mysmallgrps."));
			fi;

    elif Length(arg) > 1 then Error("Too many arguments: input has to be an integer.");
    fi;
end);

######################################################
##IdSOTGroup takes in a group G (that is, IsGroup(G) = true) of order n such that SOTGroupIsAvailable(n) = true and determines its SOT-group ID.
	##That is, it outputs an ordered pair (n, i) where m = |G| and i is the position of G in the list AllSOTGroups(n).
InstallGlobalFunction( IdSOTGroup, function(group)
	local length, n, PF, fac, k, p, q, r;
		if HasSOTGroup_id(group) then return SOTGroup_id(group); fi;
    n := Size(group);
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return msg.IdPGroup(group);
		fi;

		if length = 2 and Length(fac) = 2 then
			return msg.IdGroupPQ(group);
		elif length = 3 and Length(fac) = 2 then
			return msg.IdGroupP2Q(group);
		elif length = 3 and Length(fac) = 3 then
			return msg.IdGroupPQR(group);
		elif length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return msg.IdGroupP2Q2(group);
		elif length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return msg.IdGroupP3Q(group);
		elif length = 4 and Length(fac) = 3 then
			return msg.IdGroupP2QR(group);
		elif length = 4 and Length(fac) = 4 then
			if USE_pqrsII = true then
				return msg.IdGroupPQRSII(group);
			else
				return msg.IdGroupPQRS(group);
			fi;
		elif length = 5 and List(fac, x -> x[2]) in [ [1, 4], [4, 1]] then
			return msg.IdGroupP4Q(group);
		else
			Print(("Groups of order "), n, (" is not available in mysmallgrps: MyIdSmallGroup (#) determines groups of order # up to isomorphism, where # factorises into at most 4 primes or is of the form p^4q, where p, q are distinct primes."));
		fi;
end);
