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
		else 										 return true;
		fi;
		Print("checked ",n,"\n");
end;



###### some order test functions

msg.isp2q2:=x-> List( Collected(FactorsInt(x)),x->x[2]) = [2,2];;
msg.isp2qr:=x-> List( Collected(FactorsInt(x)),x->x[2])  in [[1,1,2],[1,2,1],[2,1,1]];;
msg.isp3q:=x-> List( Collected(FactorsInt(x)),x->x[2])  in [[3,1],[1,3]];;


