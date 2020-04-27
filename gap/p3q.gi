deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;

deltafunction := function(x, y)
  local w;
    if x = y then w := 1;
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
InstallGlobalFunction( allGroupsP3Q, function(n)
    local fac, p, q, case1, case2, case3, case4, s;
      s := [];
      fac := Factors(n);
      if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
        Error("Argument must be of the form of p^3q"); fi;
      p := fac[2];
      if fac[1] = fac[2] then
      q := fac[4]; elif fac[3] = fac[4] then
      q := fac[1]; fi;

############ add abelian groups in:
      Append(s, [AbelianGroup([n]), AbelianGroup([p^2, p*q]), AbelianGroup([p, p, p*q])]);

############ case 1: no normal Sylow subgroup -- necessarily n = 24
      if n = 24 then Add(s, PcpGroupToPcGroup(Image(IsomorphismPcpGroup(SymmetricGroup(4))))); fi;

############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
      case2 := function(p, q)
        local G1, G2, G3, G4, l;
          l := [];
          G1 := function(p, q)
            local coll, G;
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, p);
              SetRelativeOrder(coll, 2, p);
              SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, q);
              SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
              G := PcpGroupByCollector(coll);
            return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
          end;

          G2 := function(p, q)
            local coll, G;
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, p);
  						SetRelativeOrder(coll, 2, p);
  						SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, q);
  						SetPower(coll, 1, [3, 1]);
  						SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
  						G := PcpGroupByCollector(coll);
  					return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
  				end;

          G3 := function(q)
            local coll, G;
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, 2);
              SetRelativeOrder(coll, 2, 2);
              SetRelativeOrder(coll, 3, 2);
              SetRelativeOrder(coll, 4, q);
              SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
              G := PcpGroupByCollector(coll);
            return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
          end;

          G4 := function(q)
            local coll, G;
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, 2);
              SetRelativeOrder(coll, 2, 2);
              SetRelativeOrder(coll, 3, 2);
              SetRelativeOrder(coll, 4, q);
              SetPower(coll, 1, [3, 1]);
              SetPower(coll, 2, [3, 1]);
              SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
              G := PcpGroupByCollector(coll);
            return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
          end;

          if p > 2 then Append(l, [G1(p, q), G2(p, q)]);
          else Append(l, [G3(q), G4(q)]); fi;

        return l;
      end;
############ case 2 always exists
    Append(s, case2(p, q));

############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
      case3 := function(p, q)
        local class1, class2, class3, class4, class5, class6, l; ## classes depending on the isom type of P
              l := [];
              ## class 1: when P is cyclic, there are three isom types of semidirect products of P \ltimes Q
              class1 := function(p, q)
                local list, G1, G2, G3;
                  list := [];
                  G1 := function(p, q) ## G1 exists only when p divides (q - 1)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^((q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 4, 1, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod p = 0 then Add(list, G1(p, q)); fi;
                  G2 := function(p, q) ## G2 exists only when p^2 divides (q - 1)
                    local coll, c, r1, r2, G;
                      c := Z(q);
                      r1 := Int(c^((q-1)/p));
                      r2 := Int(c^((q-1)/(p^2)));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 4, 1, [4, r2]);
                      SetConjugate(coll, 4, 2, [4, r1]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod (p^2) = 0 then Add(list, G2(p, q)); fi;
                  G3 := function(p, q) ## G3 exists only when p^3 divides (q - 1)
                    local coll, c, r1, r2, r3, G;
                      c := Z(q);
                      r1 := Int(c^((q-1)/p));
                      r2 := Int(c^((q-1)/(p^2)));
                      r3 := Int(c^((q-1)/(p^3)));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 4, 1, [4, r3]);
                      SetConjugate(coll, 4, 2, [4, r2]);
                      SetConjugate(coll, 4, 3, [4, r1]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                if (q - 1) mod (p^3) = 0 then Add(list, G3(p, q)); fi;
                return list;
              end;
              Append(l, class1(p, q));
              ## class 2: when P = C_{p^2} \times C_p, there are three isom types of semidirect products of P \ltimes Q
              class2 := function(p, q)
                local list, G1, G2, G3;
                  list := [];
                  G1 := function(p, q) ## G1 exists only when p divides (q - 1)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^((q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetConjugate(coll, 4, 3, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod p = 0 then Add(list, G1(p, q)); fi;
                  G2 := function(p, q) ## G2 exists only when p divides (q - 1)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^((q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetConjugate(coll, 4, 1, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod p = 0 then Add(list, G2(p, q)); fi;
                  G3 := function(p, q) ## G3 exists only when p^2 divides (q - 1)
                    local coll, c, r1, r2, G;
                      c := Z(q);
                      r1 := Int(c^((q-1)/p));
                      r2 := Int(c^((q-1)/(p^2)));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 1, [2, 1]);
                      SetConjugate(coll, 4, 1, [4, r2]);
                      SetConjugate(coll, 4, 2, [4, r1]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                if (q - 1) mod (p^2) = 0 then Add(list, G3(p, q)); fi;
                return list;
              end;
              Append(l, class2(p, q));
              ## class 3: when P is elementary abelian, there is a unique isom type of P \ltimes Q
              class3 := function(p, q) ##class 3 exists only when p divides (q - 1)
                local coll, G, c, r;
                  c := Z(q);
                  r := Int(c^((q-1)/p));
                  coll := FromTheLeftCollector(4);
                  SetRelativeOrder(coll, 1, p);
                  SetRelativeOrder(coll, 2, p);
                  SetRelativeOrder(coll, 3, p);
                  SetRelativeOrder(coll, 4, q);
                  SetConjugate(coll, 4, 1, [4, r]);
                  G := PcpGroupByCollector(coll);
                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
              if (q - 1) mod p = 0 then
                Add(l, class3(p, q)); fi;
              ## class 4: when P is extraspecial + type, there is a unique isom type of P \ltimes Q
              class4 := function(p, q)
                local list, G1, G2;
                  list := [];
                  G1 := function(p, q)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^((q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetConjugate(coll, 3, 1, [2, 1, 3, 1]);
                      SetConjugate(coll, 4, 1, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                if (q - 1) mod p = 0 then
                  Add(list, G1(p, q)); fi;
                  G2 := function(q)
                    local coll, G;
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, 2);
                      SetRelativeOrder(coll, 2, 2);
                      SetRelativeOrder(coll, 3, 2);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
                      SetConjugate(coll, 4, 1, [4, q-1]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                if (q - 1) mod p = 0 and p = 2 then
                    Add(list, G2(q)); fi;
                return list;
              end;
            if (q - 1) mod p = 0 then
              Append(l, class4(p, q)); fi;
              ## class 5: when P is extraspecial - type, there is a unique isom type of P \ltimes Q
              class5 := function(p, q)
                local list, t, G1, G2;
                  list := [];
                  G1 := function(k, p, q)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^(k*(q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
                      SetConjugate(coll, 4, 1, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod p = 0 and p > 2 then for t in [1..p-1]
                    do Add(list, G1(t, p, q)); od; fi;
                  G2 := function(p, q)
                    local coll, c, r, G;
                      c := Z(q);
                      r := Int(c^((q-1)/p));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, p);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, q);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
                      SetConjugate(coll, 4, 2, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;
                  if (q - 1) mod p = 0 and p > 2 then
                    Add(list, G2(p, q)); fi;
                  return list;
                end;
              if (q - 1) mod p = 0 and p > 2 then
                Append(l, class5(p, q)); fi;
              ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
              class6 := function(q)
                local coll, G;
                  coll := FromTheLeftCollector(4);
                  SetRelativeOrder(coll, 1, 2);
                  SetRelativeOrder(coll, 2, 2);
                  SetRelativeOrder(coll, 3, 2);
                  SetRelativeOrder(coll, 4, q);
                  SetPower(coll, 1, [3, 1]);
                  SetPower(coll, 2, [3, 1]);
                  SetConjugate(coll, 2, 1, [2, 1, 3, 1]);
                  SetConjugate(coll, 4, 1, [4, q - 1]);
                  G := PcpGroupByCollector(coll);
                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
            if p = 2 and q > p then
              Add(l, class6(q)); fi;
            return l;
            end;
############ case 3 exists only when (q - 1) mod p = 0
    if (q - 1) mod p = 0 then Append(s, case3(p, q)); fi;
## all above checked for x in Filtered(Primes, x-> x>8) do Print("checked ", x, ", ", testMySmallGroups(8*x), "\n"); od;

############ case 4: nonabelian and only the Sylow p-subgroup is normal
      case4 := function(p, q)
        local class1, class2, class3, class4, class5, class6, class7, l; ## classes depending on the isom type of P
              l := [];
              ## class 1: when P is cyclic, there is a unique isom type of semidirect products of Q \ltimes P
              class1 := function(p, q)
                local coll, i, ii, q1, r3, a, b, G;
                  a := ZmodnZObj(Int(Z(p)),p^3);
                  if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
                  r3 := Int(b^((p^3-p^2)/q));
                  i := r3 mod p;
                  ii := (r3 - i)/p mod p;
                  q1 := ((r3 - i)/p - ii)/p;
                  coll := FromTheLeftCollector(4);
                  SetRelativeOrder(coll, 1, q);
                  SetRelativeOrder(coll, 2, p);
                  SetRelativeOrder(coll, 3, p);
                  SetRelativeOrder(coll, 4, p);
                  SetPower(coll, 2, [3, 1]);
                  SetPower(coll, 3, [4, 1]);
                  SetConjugate(coll, 2, 1, [2, i, 3, ii, 4, q1]);
                  SetConjugate(coll, 3, 1, [3, i, 4, ii]);
                  SetConjugate(coll, 4, 1, [4, i]);
                  G := PcpGroupByCollector(coll);
                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;

              if (p - 1) mod q = 0 then
                Add(l, class1(p, q)); fi;

              ## class 2: when P = C_{p^2} \times C_p, there are (q + 1) isomorphism types of Q \ltimes P
              class2 := function(p, q)
                local list, G1, G2, G3;
                  list := [];
                  G1 := function(p, q)  ## C_q \ltimes C_p \times C_{p^2}
                    local coll, G, c, r;
                      c := Z(p);
                      r := Int(c^((p-1)/q));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetPower(coll, 3, [4, 1]);
                      SetConjugate(coll, 2, 1, [2, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

                  G2 := function(p, q)  ## C_q \ltimes C_{p^2} \times C_p
                    local coll, G, a, b, r, ii, qq;
                      a := ZmodnZObj(Int(Z(p)),p^2);
                      if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
                      r := Int(b^((p^2-p)/q));
                      ii := r mod p;
                      qq := (r - ii)/p;
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetPower(coll, 2, [3, 1]);
                      SetConjugate(coll, 2, 1, [2, ii, 3, qq]);
                      SetConjugate(coll, 3, 1, [3, ii]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G2(p, q)); fi;

                  G3 := function(p, q)  ## C_q \ltimes (C_{p^2} \times C_p)
                    local tmp, t, Gtmp;
                      tmp := [];
                      Gtmp := function(k, p, q)
                        local coll, G, a, b, r, rr, ii, qq;
                          a := ZmodnZObj(Int(Z(p)),p^2);
                          if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
                          r := Int(b^(k*(p^2-p)/q));
                          rr := (Int(b^((p^2-p)/q))) mod p;
                          ii := r mod p;
                          qq := (r - ii)/p;
                          coll := FromTheLeftCollector(4);
                          SetRelativeOrder(coll, 1, q);
                          SetRelativeOrder(coll, 2, p);
                          SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
                          SetPower(coll, 2, [3, 1]);
                          SetConjugate(coll, 2, 1, [2, ii, 3, qq]);
                          SetConjugate(coll, 3, 1, [3, ii]);
                          SetConjugate(coll, 4, 1, [4, rr]);
                          G := PcpGroupByCollector(coll);
                        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                      end;
                    for t in [1.. q - 1] do Add(tmp, Gtmp(t, p, q)); od;
                    return tmp;
                  end;

                  if (p - 1 ) mod q = 0 then Append(list, G3(p, q)); fi;
                return list;
              end;

              if (p - 1) mod q = 0 then
                  Append(l, class2(p, q)); fi;

              ## class 3: when P is elementary abelian
              class3 := function(p, q)
                local list, G1, G2, G3, G4, G5;
                  list := [];
                  G1 := function(p, q) ## C_q \ltimes C_p \times C_p^2
                    local coll, c, r, G;
                      c := Z(p);
                      r := Int(c^((p - 1)/q));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                      SetRelativeOrder(coll, 2, p);
                      SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetConjugate(coll, 4, 1, [4, r]);
                      G := PcpGroupByCollector(coll);
                    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

                  G2 := function(p, q) ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
                    local tmp, t, Gtmp;
                      tmp := [];
                      Gtmp := function(k, p, q)
                        local coll, r, a, l, j, i, G;
                          r:= Z(p);
                          a:= Int(r^((p-1)/q));
                          l:= Z(q);
                          a:= Int(r^((p-1)/q));
                          l:= Z(q);
           			          i:= Int(l^k);
           			          j:= Int(r^(i*(p-1)/q));
           			          coll := FromTheLeftCollector(4);
           			          SetRelativeOrder(coll, 1, q);
           			          SetRelativeOrder(coll, 2, p);
           			          SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
           			          SetConjugate(coll, 2, 1, [2, a]);
           			          SetConjugate(coll, 3, 1, [3, j]);
           			          G := PcpGroupByCollector(coll);
           		         return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
           		       end;
                     if (p - 1) mod q = 0 and q > 2 then for t in [0..(q-1)/2] do Add(tmp, Gtmp(t, p, q)); od; fi;
                     if q = 2 then Add(tmp, Gtmp(0, p, 2)); fi;
                     return tmp;
                  end;

                  if (p - 1) mod q = 0 then Append(list, G2(p, q)); fi;

                  G3 := function(p, q) ## (C_q \ltimes C_p^2) \times C_p when q | (p + 1)
                    local mat, G, coll;
              		    mat := msg.QthRootGL2P(p, q);
              		    coll := FromTheLeftCollector(4);
              		    SetRelativeOrder(coll, 1, q);
              		    SetRelativeOrder(coll, 2, p);
              		    SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
              		    SetConjugate(coll, 2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]);
              	      SetConjugate(coll, 3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]);
              		    G := PcpGroupByCollector(coll);
              	    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p + 1) mod q = 0 and q > 2 then Add(list, G3(p, q)); fi;


                  G4 := function(p, q) ## (C_q \ltimes C_p^3) when q | (p - 1)
                    local a, r, t, tmp, Gtmp1, Gtmp2, Gtmp3, func, Gtmp4;
                      tmp :=[];
                      a := Int(Z(p)^((p-1)/q));
                      r := Z(q);
                      Gtmp1 := function(i, p, q)
                        local ltmp, coll, G, x, k;
                          ltmp := [];
                          x := Int(r^i);
                          k := Int(Z(p)^(x*(p-1)/q));
                          coll := FromTheLeftCollector(4);
                          SetRelativeOrder(coll, 1, q);
                          SetRelativeOrder(coll, 2, p);
                  		    SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
                          SetConjugate(coll, 2, 1, [2, a]);
                          SetConjugate(coll, 3, 1, [3, a]);
                          SetConjugate(coll, 4, 1, [4, k]);
                          G := PcpGroupByCollector(coll);
                        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                      end;

                      if q = 2 then Add(tmp, Gtmp1(0, p, q)); fi;
                      if (p - 1) mod 3 = 0 and q = 3 then
                        for t in [0, 1] do Add(tmp, Gtmp1(t, p, q)); od; fi;
                      if (p - 1) mod q = 0 and q > 3 then
                        for t in Filtered([1..q-2], x-> not x = (q-1)/2)
                          do Add(tmp, Gtmp1(t, p, q)); od; fi;

                      Gtmp2 := function(i, p, q)
                        local coll, G, x, y, k, k2;
                          x := Int(r^i);
                          y := Int(r^(-i));
                          k := Int(Z(p)^(x*(p-1)/q));
                          k2 := Int(Z(p)^(y*(p-1)/q));
                          coll := FromTheLeftCollector(4);
                          SetRelativeOrder(coll, 1, q);
                          SetRelativeOrder(coll, 2, p);
                    		   SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
                          SetConjugate(coll, 2, 1, [2, a]);
                          SetConjugate(coll, 3, 1, [3, k]);
                          SetConjugate(coll, 4, 1, [4, k2]);
                          G := PcpGroupByCollector(coll);
                        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                      end;

                      if (p - 1) mod q = 0 and q mod 3 = 1 then
                        for t in Filtered([1..(q-1)/2], x->not x = (q-1)/3 and not x = 2*(q-1)/3)
                          do Add(tmp, Gtmp2(t, p, q)); od; fi;
                      if (p - 1) mod q = 0 and q mod 3 = 2 and q > 2 then
                        for t in [1..(q-1)/2]
                          do Add(tmp, Gtmp2(t, p, q)); od; fi;

                      Gtmp3 := function(i, p, q)
                        local coll, G, x, y, k, k2;
                          x := Int(r^i);
                          y := Int(r^(-i));
                          k := Int(Z(p)^(x*(p-1)/q));
                          k2 := Int(Z(p)^(y*(p-1)/q));
                          coll := FromTheLeftCollector(4);
                          SetRelativeOrder(coll, 1, q);
                          SetRelativeOrder(coll, 2, p);
                    		   SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
                          SetConjugate(coll, 2, 1, [2, a]);
                          SetConjugate(coll, 3, 1, [3, k]);
                          SetConjugate(coll, 4, 1, [4, k2]);
                          G := PcpGroupByCollector(coll);
                        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                      end;

                      if (p - 1) mod q = 0 and q mod 3 = 1 then for t in [0, (q-1)/3] do Add(tmp, Gtmp3(t, p, q)); od; fi;
                      if (p - 1) mod q = 0 and q > 3 and q mod 3 = 2 then Add(tmp, Gtmp3(0, p, q)); fi;

                    func := function(q)
                      local i, j, k, x, ll;
                        ll := [];
                        for i in [1..q-2] do
                          for j in [i+1..q-2] do
                            for k in [j+1..q-2] do
                              if (i+j+k) mod (q-1) = 0 then Add(ll, [-i mod (q-1), j, k]); fi;
                              od;
                            od;
                          od;
                        return List(ll, x->[x[1],x[2]]);
                      end;

                      Gtmp4 := function(i, p, q)
                        local coll, G, x, y, k, k2;
                          x := Int(r^(i[1]));
                          y := Int(r^(i[2]));
                          k := Int(Z(p)^(x*(p-1)/q));
                          k2 := Int(Z(p)^(y*(p-1)/q));
                          coll := FromTheLeftCollector(4);
                          SetRelativeOrder(coll, 1, q);
                          SetRelativeOrder(coll, 2, p);
                          SetRelativeOrder(coll, 3, p);
                          SetRelativeOrder(coll, 4, p);
                          SetConjugate(coll, 2, 1, [2, a]);
                          SetConjugate(coll, 3, 1, [3, k]);
                          SetConjugate(coll, 4, 1, [4, k2]);
                          G := PcpGroupByCollector(coll);
                        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                      end;

                      if (p - 1) mod q = 0 and q > 3 then for t in func(q) do Add(tmp, Gtmp4(t, p, q)); od; fi;

                    return tmp;
                  end;

                  if (p - 1) mod q = 0 then Append(list, G4(p, q)); fi;

                  G5 := function(p, q) ## (C_q \ltimes C_p^3) when q | (p^2 + p + 1)
                    local mat, coll, G;
                      mat := msg.QthRootGL3P(p, q);
                      coll := FromTheLeftCollector(4);
              		    SetRelativeOrder(coll, 1, q);
              		    SetRelativeOrder(coll, 2, p);
              		    SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
              		    SetConjugate(coll, 2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1]), 4, Int(mat[3][1])]);
              	      SetConjugate(coll, 3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2]), 4, Int(mat[3][2])]);
                      SetConjugate(coll, 4, 1, [2, Int(mat[1][3]), 3, Int(mat[2][3]), 4, Int(mat[3][3])]);
              		    G := PcpGroupByCollector(coll);
              	    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p^2 + p + 1 ) mod q = 0 and q > 3 then Add(list, G5(p, q)); fi;
                return list;
              end;

              if (p^3 - 1) mod q = 0 or (p^2 - 1) mod q = 0 then
                Append(l, class3(p, q)); fi;

              class4 := function(p, q) ##when P is extraspecial of type +,
                local list, t, G1, G2, G3, G4, G5;
                  list := [];
                  G1 := function(p, q) ## q | (p - 1), Z(G) = C_p
                    local coll, G, r, a, b;
                      r := Z(p);
                      a := Int(r^((p-1)/q));
                      b := Int(r^((1-p)/q));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
              		    SetRelativeOrder(coll, 2, p);
              		    SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 3, 1, [3, a]);
                      SetConjugate(coll, 2, 1, [2, b]);
                      G := PcpGroupByCollector(coll);
              	    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

                  G2 := function(p, q) ## q | (p - 1), Z(G) = 1
                    local coll, G, r, a;
                      r := Z(p);
                      a := Int(r^((p-1)/q));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                		  SetRelativeOrder(coll, 2, p);
                		  SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 4, 1, [4, a]);
                      SetConjugate(coll, 2, 1, [2, a]);
                      G := PcpGroupByCollector(coll);
                	   return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G2(p, q)); fi;

                  G3 := function(i, p, q) ## q | (p - 1), Z(G) = 1
                    local r, a, b, c, coll, G;
                      r := Z(p);
                      a := Int(r^((p-1)/q));
                      b := Int(r^(i*(p-1)/q));
                      c := Int(r^((q+1-i)*(p-1)/q));
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                		  SetRelativeOrder(coll, 2, p);
                		  SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 4, 1, [4, a]);
                      SetConjugate(coll, 3, 1, [3, b]);
                      SetConjugate(coll, 2, 1, [2, c]);
                      G := PcpGroupByCollector(coll);
                	   return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 and q > 2 then for t in [2..(q+1)/2] do
                    Add(list, G3(t, p, q)); od; fi;

                  G4 := function(p, q) ## q | (p + 1), Z(G) = C_p
                    local coll, G, mat;
                      mat := msg.QthRootGL2P(p, q);
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                  		SetRelativeOrder(coll, 2, p);
                  		SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]);
                      SetConjugate(coll, 3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]);
                      G := PcpGroupByCollector(coll);
                	  return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p + 1) mod q = 0 and q > 2 and p > 2 then Add(list, G4(p, q)); fi;

                  return list;
                end;

                if (p^2 - 1) mod q = 0 then
                  Append(l, class4(p, q)); fi;

              class5 := function(p, q) ##when P is extraspecial of type -,
                local list, G1;
                  list := [];
                  G1 := function(p, q)
                    local coll, a, b, r, qq, ii, G;
                      a := ZmodnZObj(Int(Z(p)),p^2);
                      if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
                      r := Int(b^(p*(p-1)/q));
                      ii := r mod p;
                      qq := (r - ii)/p;
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, q);
                  		SetRelativeOrder(coll, 2, p);
                  		SetRelativeOrder(coll, 3, p);
                      SetRelativeOrder(coll, 4, p);
                      SetPower(coll, 3, [4, 1]);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 3, 1, [3, ii, 4, qq]);
                      SetConjugate(coll, 4, 1, [4, ii]);
                      G := PcpGroupByCollector(coll);
                	  return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

                  return list;
                end;

                if (p - 1) mod q = 0 then
                  Append(l, class5(p, q)); fi;

              class6 := function(p, q) ## special cases for p = 2 and q = 3
                local list, G1;
                  list := [];

                  G1 := function(p, q)
                    local coll, G;
                      coll := FromTheLeftCollector(4);
                      SetRelativeOrder(coll, 1, 3);
                  		SetRelativeOrder(coll, 2, 2);
                  		SetRelativeOrder(coll, 3, 2);
                      SetRelativeOrder(coll, 4, 2);
                      SetPower(coll, 2, [4, 1]);
                      SetPower(coll, 3, [4, 1]);
                      SetConjugate(coll, 3, 2, [3, 1, 4, 1]);
                      SetConjugate(coll, 2, 1, [3, 1]);
                      SetConjugate(coll, 3, 1, [2, 1, 3, 1]);
                      G := PcpGroupByCollector(coll);
                	  return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                  end;

                  if p = 2 and q = 3 then Add(list, G1(p, q)); fi;

                  return list;
                end;

                if p = 2 and q = 3 then
                  Append(l, class6(p, q)); fi;


                return l;
              end;

              Append(s, case4(p, q));

              return s;
            end);

######################################################
    NumberGroupsP3Q := function(n)
      local fac, p, q, m, s;
        s := [];
        fac := Factors(n);
        if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
          Error("Argument must be of the form of p^3q"); fi;
        p := fac[2];
        if fac[1] = fac[2] then
        q := fac[4]; elif fac[3] = fac[4] then
        q := fac[1]; fi;

        if n mod 2 = 1 and q > 3 then
          m := 5 + (5+p)*deltaDivisibility((q-1), p) + 2*deltaDivisibility((q-1), p^2)
            + deltaDivisibility((q-1), p^3) + (36+q^2+13*q+4*deltaDivisibility((q-1),3))*deltaDivisibility((p-1), q)/6
            + 2*deltaDivisibility((p+1), q) + deltaDivisibility((p^2+p+1), q);
          elif n mod 2 = 1 and q = 3 then
            m := 5 + (5+p)*deltaDivisibility((q-1), p) + 2*deltaDivisibility((q-1), p^2)
              + deltaDivisibility((q-1), p^3) + (36+q^2+13*q+4*deltaDivisibility((q-1),3))*deltaDivisibility((p-1), q)/6
              + 2*deltaDivisibility((p+1), q);
            else m := 5 + 7*deltafunction(p,2) + 2*deltaDivisibility((q-1),4) + deltaDivisibility((q-1), 8)
              + 10*deltafunction(q,2) + 3*deltafunction(n,24) + deltafunction(n,56); fi;
        return m;
      end;
