InstallGlobalFunction( MySmallGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return msg.lowpowerPGroups(p, k);
		fi;

		if length = 2 and Length(fac) = 2 then
			return msg.allGroupsPQ(n);
		fi;

		if length = 3 and Length(fac) = 2 then
			return msg.allGroupsP2Q(n);
		fi;

		if length = 3 and Length(fac) = 3 then
			return msg.allGroupsPQR(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return msg.allGroupsP2Q2(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return msg.allGroupsP3Q(n);
		fi;

		if length = 4 and Length(fac) = 3 then
			return msg.allGroupsP2QR(n);
		fi;

		if length = 4 and Length(fac) = 4 then
			return msg.allGroupsPQRS(n);
		fi;

		if length > 4 then
			Print(("Groups of order "), n, (" is not available in mysmallgrps: MySmallGroups (#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes."));
		fi;
end);
############################################################################
InstallGlobalFunction( MyNumberOfGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			if length < 5 then
				return msg.NumberPGroups(n);
			fi;
		fi;

		if length = 2 and Length(fac) = 2 then
			return msg.NumberGroupsPQ(n);
		fi;

		if length = 3 and Length(fac) = 2 then
			return msg.NumberGroupsP2Q(n);
		fi;

		if length = 3 and Length(fac) = 3 then
			return msg.NumberGroupsPQR(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return msg.NumberGroupsP2Q2(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return msg.NumberGroupsP3Q(n);
		fi;

		if length = 4 and Length(fac) = 3 then
			return msg.NumberGroupsP2QR(n);
		fi;

		if length = 4 and Length(fac) = 4 then
			return msg.NumberGroupsPQRS(n);
		fi;

		if length > 4 then
			Print(("Order "), n, (" is not available in mysmallgrps: MyNumberOfGroups(#) returns the number of isomorphism types of groups of order that factorises into at most 4 primes."));
		fi;
	end);

############################################################################
InstallGlobalFunction( MySmallGroupIsAvailable, function(n) ## tells whether the order is available for construction
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if length > 4 then return false; fi;
		return true;
end);
############################################################################
InstallGlobalFunction( MySmallGroup, function(n, i)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if i < (MyNumberOfGroups(n) + 1) then
			if Length(fac) = 1 then
				p := PF[1];
				k := length;
				return msg.PGroup(p, k, i);
			fi;

			if length = 2 and Length(fac) = 2 then
				return msg.GroupPQ(n, i);
			fi;

			if length = 3 and Length(fac) = 2 then
				return msg.GroupP2Q(n, i);
			fi;

			if length = 3 and Length(fac) = 3 then
				return msg.GroupPQR(n, i);
			fi;

			if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
				return msg.GroupP2Q2(n, i);
			fi;

			if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
				return msg.GroupP3Q(n, i);
			fi;

			if length = 4 and Length(fac) = 3 then
				return msg.GroupP2QR(n, i);
			fi;

			if length = 4 and Length(fac) = 4 then
				return msg.GroupPQRS(n, i);
			fi;

			if length > 4 then
				Print(("Groups of order "), n, (" is not available in mysmallgrps."));
			fi;
		fi;

		if i > MyNumberOfGroups(n) then
			Print(("Wrong input: there are "), MyNumberOfGroups(n), (" isomorphism types of groups of order "), n, ("."));
		fi;

end);
############################################################################
InstallGlobalFunction( MySmallGroupsInformation, function(arg)
	local length, PF, fac, n, k, p, q, r;
		if Length(arg) = 0 then
			Print("MySmallGroups(#) constructs all groups of order # up to isomorphism, where # factorises into at most 4 primes.");
    fi;
		if Length(arg) = 1 then
			n := arg[1];
      PF := Factors(n);
  		length := Length(PF);
  		fac := Collected(Factors(n));

  		if Length(fac) = 1 then ##p-groups
  			p := PF[1];
  			k := length;
  			if k = 1 then Print(("There is a unique group of order"), n, ("up to isomorphism, and it is cyclic.") );
  			fi;
  			if k = 2 then Print(("There are two isomorphism types of p-groups of order "),n,(": there is one cyclic group, and one elementary abelian group."));
  			fi;
  			if k = 3 then Print(("There are five isomorpshim types of p-groups of order "), n, (": there are 3 abelian groups, and 3 extraspecial groups."));
  			fi;
  			if k = 4 then
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
  		fi;

  		if length = 3 and Length(fac) = 2 then
  			if not (PF[1] - 1) mod PF[3] = 0 and not (PF[3] - 1) mod PF[1] = 0 then
  				Print(("There are two isomorphism types of order "), n, (": one is cyclic, and one is isomorphic to AbelianGroup("), p*q, p, (")."));
  			else Print(("There are "), msg.NumberGroupsP2Q(n), (" isomorphism types of groups of order "), n, ("."));
  			fi;
  		fi;

  		if length = 3 and Length(fac) = 3 then
  			Print(("There are "), msg.NumberGroupsPQR(n), (" isomorphism types of squarefree groups of order "), n, ("."));
  		fi;

  		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
  			Print(("There are "), msg.NumberGroupsP2Q2(n), (" isomorphism types of groups of order "), n, ("."));
  		fi;

  		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
  			Print(("There are "), msg.NumberGroupsP3Q(n), (" isomorphism types of groups of order "), n, ("."));
  		fi;

  		if length = 4 and Length(fac) = 3 then
  			Print(("There are "), msg.NumberGroupsP2QR(n), (" isomorphism types of groups of order "), n, ("."));
  		fi;

			if length = 4 and Length(fac) = 4 then
				Print(("There are "), msg.NumberGroupsPQRS(n), (" isomorphism types of groups of order "), n, ("."));
  		fi;

			if length > 4 then
				Print(("Order "), n, (" is not available in mysmallgrps."));
			fi;

    elif Length(arg) > 1 then Error("Too many arguments: input has to be an integer.");
    fi;
end);
