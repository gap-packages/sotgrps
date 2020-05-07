USE_NC := false;
USE_PCP := false;
############################################################################
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
############################################################################
msg.deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
  ############################################################################
msg.QthRootGL2P := function(p, q)
  local a, b;
    if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^2-1) mod q = 0 then
  	 Error("Arguments has to be primes p, q, where q divides (p^2 - 1).\n");
  	 else
  	 a := PrimitiveElement(GF(p^2));
  	 b := a^((p^2-1)/q);
  	fi;
  return [ [0, 1], [-b^(p+1), b+b^p] ] * One(GF(p));
end;

############################################################################
msg.QsquaredthRootGL2P := function(p, q)
  local a, b;
   	if not Gcd(p,q)=1 or not (p^2-1) mod (q^2) = 0 then
   	 Error("Arguments has to be primes p, q, where q^2 divides (p^2 - 1).\n");
   	 else
   	 a := PrimitiveElement(GF(p^2));
   	 b := a^((p^2-1)/(q^2));
   	fi;
  return [ [0, 1], [-b^(p+1), b+b^p] ] * One(GF(p));
end;
############################################################################
msg.deltafunction := function(x, y)
  local w;
    if x = y then w := 1;
    else w := 0; fi;
  return w;
  end;
############################################################################
msg.groupofunitsP2 := function(p)
  local l;
    l := Filtered([1..p^2], x->not x mod p = 0);
    return l;
  end;

############################################################################
msg.QthRootGL3P := function(p, q)
  local a, b;
  if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^3-1) mod q = 0 then
   Error("Arguments has to be primes p, q, where q divides (p^3 - 1).\n");
  else
    a := PrimitiveElement(GF(p^3));
    b := a^((p^3-1)/q);
  fi;
  return [ [0, 0, 1], [1, 0, -b^(p+1)-b^(p^2+1)-b^(p^2+p)], [0, 1, b+b^p+b^(p^2)] ] * One(GF(p));
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

############################################################################
