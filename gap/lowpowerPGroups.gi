
############################################################################
InstallGlobalFunction( lowpowerPGroups, function(p, k)
	local list, allGrpsP, allGrpsP2, allGrpsP3, allGrpsP4;

			allGrpsP := function(p)
				local list;
				list := [];
				Add(list, AbelianGroup([p]));
				return list;
			end;
#####################################
			allGrpsP2 := function(p)
				local list;
				list := [];
				Add(list, AbelianGroup([p^2]));
				Add(list, AbelianGroup([p, p]));
				return list;
			end;
#####################################
			allGrpsP3 := function(p)
				local list, G1, G2, case1, case2, G5;
				list :=[];
				G1 := AbelianGroup([p^3]);
				G2 := AbelianGroup([p, p^2]);
				G5 := AbelianGroup([p, p, p]);
				Append(list, [G1, G2, G5]);
		##case1 is when p =2

				case1 := function(p)
					local G3, G4, s;
					s := [];
					G3 := function(p)
						local coll, G;
							coll := FromTheLeftCollector(3);
							SetRelativeOrder(coll, 1, 2);
							SetRelativeOrder(coll, 2, 2);
							SetRelativeOrder(coll, 3, 2);
							SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
							G := PcpGroupByCollector(coll);
						return PcpGroupToPcGroup(G);
					end;

					Add(s, G3(p));

					G4 := function(p)
						local coll, G;
							coll := FromTheLeftCollector(3);
							SetRelativeOrder(coll, 1, 2);
							SetRelativeOrder(coll, 2, 2);
							SetRelativeOrder(coll, 3, 2);
							SetPower(coll, 1, [3, 1]);
              SetPower(coll, 2, [3, 1]);
							SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
							G := PcpGroupByCollector(coll);
						return PcpGroupToPcGroup(G);
					end;
					Add(s, G4(p));
				return s;
				end;

				if p = 2 then Append(list, case1(p)); fi;

			##case2 is when p > 2

				case2	:= function(p)
					local G3, G4, s;
					 	s:= [];

						G3 := function(p)
							local coll, G;
								coll := FromTheLeftCollector(3);
								SetRelativeOrder(coll, 1, p);
								SetRelativeOrder(coll, 2, p);
								SetRelativeOrder(coll, 3, p);
								SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
								G := PcpGroupByCollector(coll);
							return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
						end;

						Add(s, G3(p));

						G4 := function(p)
							local coll, G;
								coll := FromTheLeftCollector(3);
								SetRelativeOrder(coll, 1, p);
								SetRelativeOrder(coll, 2, p);
								SetRelativeOrder(coll, 3, p);
								SetPower(coll, 1, [3, 1]);
								SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
								G := PcpGroupByCollector(coll);
							return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
						end;

						Add(list, G4(p));

				return s;
				end;

				if p > 2 then Append(list, case2(p)); fi;

				return list;
			end;
#####################################

			##construct groups of order p^4
			allGrpsP4:=function(p)
			local list, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20;
				list := [];
				 Add(list, AbelianGroup([p^4]));
				 Add(list, AbelianGroup([p^3, p]));
				 Add(list, AbelianGroup([p^2, p^2]));
				 Add(list, AbelianGroup([p^2, p, p]));
				 Add(list, AbelianGroup([p, p, p, p]));

			  G1 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll, 1, p);
			      SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
			      SetRelativeOrder(coll, 4, p);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 4, 1, [3, 1, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			G2 := function(p)
				local coll, G;
					coll:=FromTheLeftCollector(4);
					SetRelativeOrder(coll, 1, p);
					SetRelativeOrder(coll, 2, p);
					SetRelativeOrder(coll, 3, p);
					SetRelativeOrder(coll, 4, p);
					SetPower(coll, 2, [3, 1]);
					SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
					G := PcpGroupByCollector(coll);
				return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			end;
			##
			  G3 := function(p)
			    local coll, G;
						coll:=FromTheLeftCollector(4);
						SetRelativeOrder(coll, 1, p);
						SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
						SetRelativeOrder(coll, 4, p);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 2, 1, [2, 1, 3, 1, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G4 := function(p)
			    local coll, G;
						coll:=FromTheLeftCollector(4);
						SetRelativeOrder(coll, 1, p);
						SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
						SetRelativeOrder(coll, 4, p);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 2, 1, [2, 1, 4, 1]);
			      SetConjugate(coll, 4, 1, [3, 1, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G5 := function(p)
			    local i, coll, G;
			      i := Int(Z(p));
						coll:=FromTheLeftCollector(4);
						SetRelativeOrder(coll, 1, p);
						SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
						SetRelativeOrder(coll, 4, p);
						SetPower(coll, 2, [3, 1]);
						SetConjugate(coll, 2, 1, [2, 1, 4, 1]);
			      SetConjugate(coll, 4, 1, [3, i, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G6 := function(p)
			    local coll, G;
						coll:=FromTheLeftCollector(4);
						SetRelativeOrder(coll, 1, p);
						SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
						SetRelativeOrder(coll, 4, p);
			      SetPower(coll, 1, [2, 1]);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 4, 1, [3, 1, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G7 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll, 1, p);
			      SetRelativeOrder(coll, 2, p);
						SetRelativeOrder(coll, 3, p);
			      SetRelativeOrder(coll, 4, p);
			      SetPower(coll, 1, [4, 1]);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G8 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll, 1, p);
			      SetRelativeOrder(coll, 2, p);
			      SetRelativeOrder(coll, 3, p);
			      SetRelativeOrder(coll, 4, p);
			      SetConjugate(coll, 3, 1, [2, 1, 3, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G9 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll,1,p);
			      SetRelativeOrder(coll,2,p);
			      SetRelativeOrder(coll,3,p);
			      SetRelativeOrder(coll,4,p);
			      SetConjugate(coll,3,1,[2,1,3,1]);
			      SetConjugate(coll,4,1,[3,1,4,1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G10 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll,1,p);
			      SetRelativeOrder(coll,2,p);
			      SetRelativeOrder(coll,3,p);
			      SetRelativeOrder(coll,4,p);
			      SetConjugate(coll,3,1,[2,1,3,1]);
			      SetConjugate(coll,4,1,[3,1,4,1]);
			      SetPower(coll,1,[2,1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			##
			  G11 := function(p)
			    local coll, G, i;
			      i := Int(Z(p));
			      coll:=FromTheLeftCollector(4);
			      SetRelativeOrder(coll, 1, p);
			      SetRelativeOrder(coll, 2, p);
			      SetRelativeOrder(coll, 3, p);
						SetRelativeOrder(coll, 4, p);
						SetPower(coll, 1, [3, 1]);
						SetPower(coll, 2, [3, 1]);
			      SetConjugate(coll, 2, 1, [2, 1, 4, 1]);
			      SetConjugate(coll, 4, 1, [3, i, 4, 1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
			  end;
			## case: p = 2
			  G12 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(2);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,8);
			      SetConjugate(coll,2,1,[2,3]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G13 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(2);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,8);
			      SetConjugate(coll,2,1,[2,5]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G14 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(2);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,8);
			      SetConjugate(coll,2,1,[2,7]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G15 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(2);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,8);
			      SetConjugate(coll,2,1,[2,7]);
			      SetPower(coll,1,[2,4]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G16 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(3);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,4);
			      SetRelativeOrder(coll,3,2);
			      SetConjugate(coll,2,1,[2,3]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G17 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(3);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,4);
			      SetRelativeOrder(coll,3,2);
			      SetConjugate(coll,2,1,[2,1,3,1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G18 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(3);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,4);
			      SetRelativeOrder(coll,3,2);
			      SetConjugate(coll,2,1,[2,3]);
			      SetConjugate(coll,3,1,[2,2,3,1]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G19 := function(p)
			    local coll, G;
			      coll:=FromTheLeftCollector(3);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,4);
			      SetRelativeOrder(coll,3,2);
			      SetConjugate(coll,2,1,[2,3]);
			      SetPower(coll,1,[2,2]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##
			  G20 := function(p)
			    local coll, G;
			      coll := FromTheLeftCollector(3);
			      SetRelativeOrder(coll,1,2);
			      SetRelativeOrder(coll,2,4);
			      SetRelativeOrder(coll,3,2);
			      SetConjugate(coll,2,1,[2,1,3,1]);
			      SetPower(coll,1,[2,2]);
			      G := PcpGroupByCollector(coll);
			    return PcpGroupToPcGroup(RefinedPcpGroup(G));
			  end;
			##

			if p = 3 then
					    Add(list, G1(p));
					    Add(list, G2(p));
					    Add(list, G3(p));
					    Add(list, G4(p));
			        Add(list, G5(p));
					    Add(list, G6(p));
					    Add(list, G7(p));
			  		  Add(list, G8(p));
					    Add(list, G9(p));
					    Add(list, G11(p));
				elif p = 2 then
			  		  Add(list, G12(p));
					    Add(list, G13(p));
					    Add(list, G14(p));
					    Add(list, G15(p));
					    Add(list, G16(p));
					    Add(list, G17(p));
					    Add(list, G18(p));
					    Add(list, G19(p));
					    Add(list, G20(p));
					else
			        Add(list, G1(p));
					    Add(list, G2(p));
					    Add(list, G3(p));
					    Add(list, G4(p));
					    Add(list, G5(p));
					    Add(list, G6(p));
					    Add(list, G7(p));
					    Add(list, G8(p));
			        Add(list, G9(p));
					    Add(list, G10(p));
					   fi;
			  return list;
			end;
#####################################
			## now by power of p
			if k = 1 then return
			allGrpsP(p); fi;
			if k = 2 then return
			allGrpsP2(p); fi;
			if k = 3 then return
			allGrpsP3(p); fi;
			if k = 4 then return
			allGrpsP4(p); fi;
end);

############################################################################
NumberPGroups := function(n)
	local power, prime, w;
		prime := Collected(Factors(n))[1][1];
		power := Collected(Factors(n))[1][2];
		if power = 1 then w := 1; fi;
		if power = 2 then w := 2; fi;
		if power = 3 then w := 5;	fi;
		if power = 4 and prime = 2 then w := 14; fi;
		if power = 4 and prime > 2 then w := 15; fi;
	return w;
end;
