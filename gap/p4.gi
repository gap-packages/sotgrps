##################################
##construct groups of order p^4
msg.allGrpsP4:=function(p)
local s, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20;
  G1 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,3,1,[2,p,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G2 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,2,1,[2,1+p]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G3 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,2,1,[2,1,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G4 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,2,1,[2,1,3,1]);
      SetConjugate(coll,3,1,[2,p,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G5 := function(p)
    local i, coll, G;
      i := PrimitiveRootMod(p);
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,2,1,[2,1,3,1]);
      SetConjugate(coll,3,1,[2,i*p,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G6 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetPower(coll,1,[2,1]);
      SetConjugate(coll,3,1,[2,p,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G7 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetPower(coll,1,[3,1]);
      SetConjugate(coll,2,1,[2,p+1]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G8 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(4);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p);
      SetRelativeOrder(coll,3,p);
      SetRelativeOrder(coll,4,p);
      SetConjugate(coll,3,1,[2,1,3,1]);
      G := PcpGroupByCollector(coll);
    return G;
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
    return G;
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
    return G;
  end;
##
  G11 := function(p)
    local coll, G, i;
      i := PrimitiveRootMod(p);
      coll:=FromTheLeftCollector(3);
      SetRelativeOrder(coll,1,p);
      SetRelativeOrder(coll,2,p^2);
      SetRelativeOrder(coll,3,p);
      SetConjugate(coll,2,1,[2,1,3,1]);
      SetConjugate(coll,3,1,[2,i*p,3,1]);
      SetPower(coll,1,[2,p]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
## case: p = 2
  G12 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(2);
      SetRelativeOrder(coll,1,2);
      SetRelativeOrder(coll,2,8);
      SetConjugate(coll,2,1,[2,3]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G13 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(2);
      SetRelativeOrder(coll,1,2);
      SetRelativeOrder(coll,2,8);
      SetConjugate(coll,2,1,[2,5]);
      G := PcpGroupByCollector(coll);
    return G;
  end;
##
  G14 := function(p)
    local coll, G;
      coll:=FromTheLeftCollector(2);
      SetRelativeOrder(coll,1,2);
      SetRelativeOrder(coll,2,8);
      SetConjugate(coll,2,1,[2,7]);
      G := PcpGroupByCollector(coll);
    return G;
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
    return G;
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
    return G;
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
    return G;
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
    return G;
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
    return G;
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
    return G;
  end;
##
s := [];
if p = 3 then
		   Add(s, G1(p));
		   Add(s, G2(p));
		   Add(s, G3(p));
		   Add(s, G4(p));
       Add(s, G5(p));
		   Add(s, G6(p));
		   Add(s, G7(p));
  		 Add(s, G8(p));
		   Add(s, G9(p));
		   Add(s, G11(p));
	elif p = 2 then
  		 Add(s, G12(p));
		   Add(s, G13(p));
		   Add(s, G14(p));
		   Add(s, G15(p));
		   Add(s, G16(p));
		   Add(s, G17(p));
		   Add(s, G18(p));
		   Add(s, G19(p));
		   Add(s, G20(p));
		else
       Add(s, G1(p));
		   Add(s, G2(p));
		   Add(s, G3(p));
		   Add(s, G4(p));
		   Add(s, G5(p));
		   Add(s, G6(p));
		   Add(s, G7(p));
		   Add(s, G8(p));
       Add(s, G9(p));
		   Add(s, G10(p));
		   fi;
  return s;
  end;
