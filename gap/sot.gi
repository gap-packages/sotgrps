## In the following, we define the preliminary functions. In particular, the canonical generators of irreducible subgroups of Singer cycles in GL_n(p) are defined here.
## For further details about the canonical form of the cyclic irreducible groups of GL_n(p), we refer to [2, Notation 2.3].
## Globally, we use GAP's inbuilt function Z(p) to compute \sigma_p (see [2, Notation 2.3]) for the canonical primitive root modulo p (where p is a prime), and compute \rho(p, b) accordingly for b dividing (p - 1).
    ## Analogously, we compute \sigma_{p^k} by computing ZmodnZObj(Int(Z(p)), p^k) or ZmodnZObj(Int(Z(p)), p^k) + p for the canonical primitive root modulo p^k (k is a positive integer), and \rho(p^k, b) accordingly for b dividing (p - 1).
    ## The SOTGrps library overlaps with the SmallGrps library.
############################################################################
############################################################################
#
# constructs a pc/pcp group given by a list data;
# the list data encodes a polycyclic presentation of a pc group with
# relative orders data[1]; the remaining entries data[i] with i>1
# encode conjugate relations (if data[i][2] is an integer)
# or a power relation (if data[i][2] is a list
#
SOTRec.groupFromData := function(data)
  local coll, gens, conj, pw, i, j, n, G;
    n := Size(data[1]);
    if SOTRec.PCP = true then
        coll := ValueGlobal("FromTheLeftCollector")(n);
        for i in [1..n] do
          SetRelativeOrder(coll,i,data[1][i]);
        od;
        for i in [2..Length(data)] do
            if IsInt(data[i][2]) then
                SetConjugateNC(coll,data[i][1],data[i][2],data[i][3]);
            else
                SetPowerNC(coll,data[i][1],data[i][2]);
            fi;
        od;
        UpdatePolycyclicCollector(coll);

        G := ValueGlobal("PcpGroupByCollectorNC")(coll);
    else
        gens := FreeGroup(IsSyllableWordsFamily, n);;
        coll := SingleCollector(gens, data[1]);
        for i in [2..Length(data)] do
            if IsInt(data[i][2]) then
                conj := [];
                for j in [1..Length(data[i][3])/2] do
                    Add(conj, gens.(data[i][3][2*j-1])^(data[i][3][2*j]));
                od;
                SetConjugateNC(coll,data[i][1],data[i][2],Product(conj));
            else
                pw := [];;
                for j in [1..Length(data[i][2])/2] do
                    Add(pw, gens.(data[i][2][2*j-1])^(data[i][2][2*j]));
                od;
                SetPowerNC(coll,data[i][1],Product(pw));
            fi;
        od;
        UpdatePolycyclicCollector(coll);
        G := GroupByRwsNC(coll);
    fi;

    return G;
end;
############################################################################
#
# the divisibility Kronecker function \Delta_x^y
#
SOTRec.w := function(x, y)
  local w;
    if x mod y = 0 then
      w := 1;
    else
      w := 0;
    fi;
  return w;
  end;
############################################################################
#
# the matrix Irr_2(p,q) as in Notation 2.3, [DEP22]
#
SOTRec.QthRootGL2P := function(p, q)
  local a, b;
    if not Gcd(p,q)=1 or not (p^2-1) mod q = 0 then
      Error("Arguments have to be coprime (p, q), where q divides (p^2 - 1).\n");
    fi;
    a := Z(p,2);
    b := a^((p^2-1)/q);
  return [ [0, 1], [-1, b+b^p] ] * One(GF(p));
end;
############################################################################
#
#
#
SOTRec.QthRootM2P2 := function(p, q)
  local a, b, m, mat, u1, u2, u3, u4, v1, v2, v3, v4;
    if not Gcd(p,q)=1 or not (p^2-1) mod q = 0 then
      Error("Arguments have to be coprime (p, q), where q divides (p^2 - 1).\n");
    fi;
    a := Z(p,2);
    b := a^((p^2-1)/q);
    m := ([ [0, 1], [Int((-b^(p+1)) * One(GF(p))), Int((b+b^p) * One(GF(p)))] ] * ZmodnZObj(1, p^2))^p;
    u1 := Int(m[1][1]) mod p;
    u2 := Int(m[1][2]) mod p;
    v1 := Int(m[2][1]) mod p;
    v2 := Int(m[2][2]) mod p;
    u3 := (Int(m[1][1]) - u1)/p;
    u4 := (Int(m[1][2]) - u2)/p;
    v3 := (Int(m[2][1]) - v1)/p;
    v4 := (Int(m[2][2]) - v2)/p;
    mat := [ [u1, u2, 0, 0],
             [v1, v2, 0, 0],
             [u3, u4, u1, u2],
             [v3, v4, v1, v2] ];
  return mat;
end;
############################################################################
#
# the matrix Irr_2(p,q^2) as in Notation 2.3
#
SOTRec.QsquaredthRootGL2P := function(p, q)
  local a, b;
    if not Gcd(p,q)=1 or not (p^2-1) mod (q^2) = 0 then
        Error("Arguments have to be primes p, q, where q^2 divides (p^2 - 1).\n");
    fi;
    a := Z(p,2);
    b := a^((p^2-1)/(q^2));
  return [ [0, 1], [-1, b+b^p] ] * One(GF(p));
end;
############################################################################
#
# the original Kronecker delta
#
SOTRec.delta := function(x, y)
  local w;
    if x = y then
      w := 1;
    else
      w := 0;
    fi;
  return w;
  end;
############################################################################
#
# returns units in Z_{p^2}
#
SOTRec.groupofunitsP2 := function(p)
  local l;
    l := Filtered([1..p^2], x->x mod p <> 0);
    return l;
  end;

############################################################################
#
# the matrix Irr_3(p,q) as in Notation 2.3
#
SOTRec.QthRootGL3P := function(p, q)
  local a, b;
  if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^3-1) mod q = 0 then
   Error("Arguments have to be primes p, q, where q divides (p^3 - 1).\n");
  else
    a := Z(p,3);
    b := a^((p^3-1)/q);
  fi;
  return [ [0, 1, 0], [0, 0, 1], [1, -b^(p+1)-b^(p^2+1)-b^(p^2+p), b+b^p+b^(p^2)] ] * One(GF(p));
end;
############################################################################
#
# (for order p^4q, proved in the Thesis but not publised in [DEP22])
#
SOTRec.QthRootGL4P := function(p, q)
  local a, b, u, v;
  if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^2+1) mod q = 0 and p <> 3 then
   Error("Arguments have to be primes p, q, where q divides (p^2 + 1) and p <> 3.\n");
  else
    a := Z(p,4);
    b := a^((p^4-1)/q);
    u := b^(p^2+p+1)+b^(p^3+p+1)+b^(p^3+p^2+1)+b^(p^3+p^2+p);
    v := -b^(p+1)-b^(p^2+1)-b^(p^3+1)-b^(p^2+p)-b^(p^3+p)-b^(p^3+p^2);
  fi;
  return [ [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [-1, u, v, b+b^p+b^(p^2)+b^(p^3)] ] * One(GF(p));
end;
############################################################################
#
# get eigenvalues with multiplicities
#
SOTRec.EigenvaluesWithMultiplicitiesGL3P := function(mat, p)
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
#
# get eigenvalues with multiplicities
#
SOTRec.EigenvaluesWithMultiplicitiesGL4P := function(mat, p)
  local l, det, evm;
    l := Eigenvalues(GF(p), mat);
    det := DeterminantMat(mat);
    if Length(l) = 4 then
      evm := Collected(l);
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
    else
      evm := Collected([l[1], l[1], l[1], l[1]]);
    fi;
    SortBy(evm, x -> x[2]);
    return evm;
end;
############################################################################
SOTRec.EigenvaluesGL4P2 := function(mat, p)
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
    else
      evm := [ [l[1], l[1]], [l[1], l[1]] ];
    fi;
    return evm;
end;
############################################################################
############################################################################
