USE_NC := true;
USE_PCP := false;
USE_pqrsII := true;
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
msg.w := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
############################################################################
msg.QthRootGL2P := function(p, q)
  local a, b;
    if not Gcd(p,q)=1 or not (p^2-1) mod q = 0 then
  	 Error("Arguments have to be coprime (p, q), where q divides (p^2 - 1).\n");
  	 else
  	 a := PrimitiveElement(GF(p^2));
  	 b := a^((p^2-1)/q);
  	fi;
  return [ [0, 1], [-1, b+b^p] ] * One(GF(p));
end;
############################################################################
msg.QthRootM2P2 := function(p, q)
  local a, b, m, mat, u1, u2, u3, u4, v1, v2, v3, v4;
    if not Gcd(p,q)=1 or not (p^2-1) mod q = 0 then
  	 Error("Arguments have to be coprime (p, q), where q divides (p^2 - 1).\n");
  	 else
  	 a := PrimitiveElement(GF(p^2));
  	 b := a^((p^2-1)/q);
     m := ([ [0, 1], [Int((-b^(p+1)) * One(GF(p))), Int((b+b^p) * One(GF(p)))] ] * ZmodnZObj(1, p^2))^p;
     u1 := Int(m[1][1]) mod p;    u2 := Int(m[1][2]) mod p;    v1 := Int(m[2][1]) mod p;    v2 := Int(m[2][2]) mod p;
     u3 := (Int(m[1][1]) - u1)/p; u4 := (Int(m[1][2]) - u2)/p; v3 := (Int(m[2][1]) - v1)/p; v4 := (Int(m[2][2]) - v2)/p;
     mat := [ [u1, u2, 0, 0],
              [v1, v2, 0, 0],
              [u3, u4, u1, u2],
              [v3, v4, v1, v2] ];
  	fi;
  return mat;
end;
############################################################################
msg.QsquaredthRootGL2P := function(p, q)
  local a, b;
   	if not Gcd(p,q)=1 or not (p^2-1) mod (q^2) = 0 then
   	 Error("Arguments have to be primes p, q, where q^2 divides (p^2 - 1).\n");
   	 else
   	 a := PrimitiveElement(GF(p^2));
   	 b := a^((p^2-1)/(q^2));
   	fi;
  return [ [0, 1], [-1, b+b^p] ] * One(GF(p));
end;
############################################################################
msg.delta := function(x, y)
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
   Error("Arguments have to be primes p, q, where q divides (p^3 - 1).\n");
  else
    a := PrimitiveElement(GF(p^3));
    b := a^((p^3-1)/q);
  fi;
  return [ [0, 0, 1], [1, 0, -b^(p+1)-b^(p^2+1)-b^(p^2+p)], [0, 1, b+b^p+b^(p^2)] ] * One(GF(p));
end;
############################################################################
msg.QthRootGL4P := function(p, q)
  local a, b, u, v;
  if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^2+1) mod q = 0 and p <> 3 then
   Error("Arguments have to be primes p, q, where q divides (p^2 + 1).\n");
  else
    a := PrimitiveElement(GF(p^4));
    b := a^((p^4-1)/q);
    u := b^(p^2+p+1)+b^(p^3+p+1)+b^(p^3+p^2+1)+b^(p^3+p^2+p);
    v := -b^(p+1)-b^(p^2+1)-b^(p^3+1)-b^(p^2+p)-b^(p^3+p)-b^(p^3+p^2);
  fi;
  return [ [0, 0, 0, -1], [1, 0, 0, u], [0, 1, 0, v], [0, 0, 1, b+b^p+b^(p^2)+b^(p^3)] ] * One(GF(p));
end;
############################################################################
msg.EigenvaluesWithMultiplicitiesGL3P := function(mat, p)
  local l, det, evm;
    l := Eigenvalues(GF(p), mat);
    det := DeterminantMat(mat);
    if Length(l) = 3 then
      evm := Collected(l);
    elif Length(l) = 2 then
      if det = l[1]^2*l[2] then
        evm := [[l[2], 1], [l[1], 2]];
      elif det = l[2]^2*l[1] then
        evm := [[l[1], 1], [l[2], 2]];
      fi;
    elif Length(l) = 1 then
      evm := Collected([l[1], l[1], l[1]]);
    fi;
  return evm;
end;
############################################################################
msg.EigenvaluesWithMultiplicitiesGL4P := function(mat, p)
  local l, det, evm;
    l := Eigenvalues(GF(p), mat);
    det := DeterminantMat(mat);
    if Length(l) = 4 then evm := Collected(l);
    elif Length(l) = 3 then
      if l[1]^2*l[2]*l[3] = det then
        evm := Collected([l[2], l[3], l[1], l[1]]);
      elif l[1]*l[2]^2*l[3] = det then
        evm := Collected([l[1], l[3], l[2], l[2]]);
      elif l[1]*l[2]*l[3]^2 = det then
          evm := Collected([l[1], l[2], l[3], l[3]]);
      fi;
    elif Length(l) = 2 then
      if l[1]^3*l[2] = det then
        evm := Collected([l[2], l[1], l[1], l[1]]);
      elif l[1]*l[2]^3 = det then
        evm := Collected([l[1], l[2], l[2], l[2]]);
      elif l[1]^2*l[2]^2 = det then
        evm := Collected([l[1], l[1], l[2], l[2]]);
      fi;
    else evm := Collected([l[1], l[1], l[1], l[1]]);
  fi;
  SortBy(evm, x -> x[2]);
  return evm;
end;
############################################################################
msg.EigenvaluesGL4P2 := function(mat, p)
  local l, det, evm;
    l := Eigenvalues(GF(p^2), mat);
    det := DeterminantMat(mat);
    if Length(l) = 4 then
      if l[1] * l[2] = det and l[3] * l[4] = det then
        evm := [ [l[1], l[2]], [l[3], l[4]] ];
      elif l[1] * l[3] = det and l[2] * l[4] = det then
        evm := [ [l[1], l[3]], [l[2], l[4]] ];
      elif l[1] * l[4] = det and l[2] * l[3] = det then
        evm := [ [l[1], l[4]], [l[2], l[3]] ];
      fi;
    elif Length(l) = 3 then
      if l[1]^2 = det and l[2] * l[3] = det then
        evm := [ [l[1], l[1]], [l[2], l[3]] ];
      elif l[2]^2 = det and l[1] * l[3] = det then
        evm := [ [l[2], l[2]], [l[1], l[3]] ];
      elif l[3]^2 = det and l[1] * l[2] = det then
        evm := [ [l[3], l[3]], [l[1], l[2]] ];
      fi;
    elif Length(l) = 2 then
      evm := [ [l[1], l[2]], [l[1], l[2]] ];
    else evm := [ [l[1], l[1]], [l[1], l[1]] ];
  fi;
  return evm;
end;
############################################################################
msg.testAllSOTGroups := function(n)
	local mygroups, lib, duplicates, missing;
				duplicates := [];
				missing    := [];
				mygroups   := List(AllSOTGroups(n),x->IdSmallGroup(x)[2]);
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
