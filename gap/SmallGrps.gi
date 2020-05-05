USE_NC := false;
USE_PCP := false;
##############################
msg.groupFromData := function(data)
  local coll, i, j, n ,G;
   n := Size(data[1]);
   coll := FromTheLeftCollector(n);
   for i in [1..n] do SetRelativeOrder(coll,i,data[1][i]); od;
   for i in [2..Length(data)] do
      if IsInt(data[i][2]) then
         SetConjugateNC(coll,data[i][1],data[i][2],data[i][3]);
      else
         SetPowerNC(coll,data[i][1],data[i][2]);
      fi;
   od;
   UpdatePolycyclicCollector(coll);
  if USE_NC then
    G := PcpGroupByCollectorNC(coll);
  else G := PcpGroupByCollector(coll);
  fi;
  if USE_PCP = false then
    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
  else return G;
  fi;
end;
##############################
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
			return msg.NumberPGroups(n);
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
	end);

############################################################################
msg.isAvailable := function(n) ## tells whether the order is available for construction
	local length, PF, fac, k, p, q, r;
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if length > 4 then return false; fi;
		if length = 4 and Length(fac) = 4 then return false; fi;
		return true;
	end;

############################################################################
msg.testMySmallGroups := function(n)
	local mygroups, lib, duplicates, missing;
				duplicates := [];
				missing    := [];
				mygroups   := List(MySmallGroups(n),x->IdSmallGroup(x)[2]);
						lib    := [1..NumberSmallGroups(n)];
				if Size(mygroups) = NumberSmallGroups(n) and AsSet(mygroups) = lib then
					return true;
				elif not Size(mygroups) = NumberSmallGroups(n) or not AsSet(mygroups) = lib then
					Append(duplicates, List(Filtered(Collected(mygroups), x->x[2] > 1), x->x[1]));
					Print(("duplicate groups of order "), n,(" with id "), duplicates, ", ");
					 Append(missing, Filtered(lib, x-> not x in mygroups));
					Print(("missing groups of order "), n,(" with id "), missing, ".");
				fi;
end;
############################################################################
msg.isIrredundant := function(n)
	local mystuff, lib;
		mystuff := Size(MySmallGroups(n));
			  lib := NumberSmallGroups(n);
		if mystuff = lib then return true;
		else
  return false; fi;
end;
############################################################################
msg.testMyNumberSmallGroups := function(n)
	local mystuff, lib;
	 	mystuff := NumberMySmallGroups(n);
	      lib := NumberSmallGroups(n);
		if not mystuff = lib then return false;
		else 										 return true;
		fi;
	Print("checked ",n,"\n");
end;
############################################################################
msg.testIrredundancy := function(n)
	local actual, theory;
		actual := Size(MySmallGroups(n));
		theory := NumberMySmallGroups(n);
		if not actual = theory then return false;
		else 										    return true;
		fi;
		Print("checked ",n,"\n");
end;
############################################################################

############################################################################
MySmallGroupsInformation := function(arg)
	local length, PF, fac, n, k, p, q, r;
		if Length(arg) = 0 then
			Print("SmallGroups(n) constructs all groups of order n up to isomorphism, where n factorises into at most 4 primes, except for n = pqrs.");
		elif Length(n) = 1 then
			n := arg[1];
		else Error("Too many arguments: input has to be an integer.");
		fi;

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
end;
