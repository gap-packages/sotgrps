InstallGlobalFunction( SmallGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return lowpowerPGroups(p, k);
		fi;

		if length = 2 and Length(fac) = 2 then
			return allGroupsPQ(n);
		fi;

		if length = 3 and Length(fac) = 2 then
			return allGroupsP2Q(n);
		fi;

		if length = 3 and Length(fac) = 3 then
			return allGroupsPQR(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return allGroupsP2Q2(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return allGroupsP3Q(n);
		fi;

		if length = 4 and Length(fac) = 3 then
			return allGroupsP2QR(n);
		fi;
	end);

############################################################################
InstallGlobalFunction( NumberMySmallGroups, function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return NumberPGroups(n);
		fi;

		if length = 2 and Length(fac) = 2 then
			return NumberGroupsPQ(n);
		fi;

		if length = 3 and Length(fac) = 2 then
			return NumberGroupsP2Q(n);
		fi;

		if length = 3 and Length(fac) = 3 then
			return NumberGroupsPQR(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return NumberGroupsP2Q2(n);
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return NumberGroupsP3Q(n);
		fi;

		if length = 4 and Length(fac) = 3 then
			return NumberGroupsP2QR(n);
		fi;
	end);

############################################################################
isAvailable := function(n) ## tells whether the order is available for construction
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if length > 4 then return false; fi;
		if length = 4 and Length(fac) = 4 then return false; fi;
		return true;
	end;

############################################################################
testMySmallGroups := function(n)
	local mystuff, lib;
				mystuff := AsSet(List(SmallGroups(n),x->IdSmallGroup(x)[2]));
						lib := [1..NumberSmallGroups(n)];
							if mystuff = lib then return true;
							else return false; fi;
end;
############################################################################
isIrredundant := function(n)
	local mystuff, lib;
				mystuff := Size(SmallGroups(n));
				    lib := NumberSmallGroups(n);
						if mystuff = lib then return true;
						else return false; fi;
		end;
############################################################################
testMyNumberSmallGroups := function(n)
	local mystuff, lib;
	 			mystuff := NumberMySmallGroups(n);
				lib 		 := NumberSmallGroups(n);
				if not mystuff = lib then return false;
				else 										 return true;
				fi;
				Print("checked ",n,"\n");
end;
############################################################################
testIrredundancy := function(n)
	local actual, theory;
		actual := Size(SmallGroups(n));
		theory := NumberMySmallGroups(n);
		if not actual = theory then return false;
		else 										    return true;
		fi;
		Print("checked ",n,"\n");
end;
############################################################################
MySmallGroupsInformation := function()
	Print("SmallGroups(n) constructs all groups of order n up to isomorphism, where n factorises into at most 4 primes, except for n = pqrs.");
end;
############################################################################
MySmallGroupsInformation := function(n)
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));

		if Length(fac) = 1 then ##p-groups
			p := PF[1];
			k := length;
			if k = 1 then Print(("There is a unique group of order "),n(", up to isomorphism, and it is cyclic.") );
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
			if (PF[2] - 1) mod PF[1] = 1 then
				Print(("There are two isomorphism types of squarefree groups of order "), n, (": there is one abelian group, and one nonebalian group."));
			else Print(("There is a unique group of order "), n, (", up to isomorphism, and it is abelian."));
			fi;
		fi;


		if length = 3 and Length(fac) = 2 then
			if not (PF[1] - 1) mod PF[3] = 0 and not (PF[3] - 1) mod PF[1] = 0 then
				Print(("There are two isomorphism types of order "), n, (": one is cyclic, and one is isomorphic to AbelianGroup("), p*q, p, (")."));
			else Print(("There are "), NumberGroupsP2Q(n), (" isomorphism types of groups of order "), n, ("."));
			fi;
		fi;

		if length = 3 and Length(fac) = 3 then
			Print(("There are "), NumberGroupsPQR(n), (" isomorphism types of squarefree groups of order "), n, ("."));
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			Print(("There are "), NumberGroupsP2Q2(n), (" isomorphism types of groups of order "), n, ("."));
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			Print(("There are "), NumberGroupsP3Q(n), (" isomorphism types of groups of order "), n, ("."));
		fi;

		if length = 4 and Length(fac) = 3 then
			Print(("There are "), NumberGroupsP2QR(n), (" isomorphism types of groups of order "), n, ("."));
		fi;
end;
