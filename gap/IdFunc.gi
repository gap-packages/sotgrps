## Functions to identify a group of order n, where n factorises in at most 4 primes, by its SOT-group ID.
## By reversing the process of constructing a deterministically ordered list, we identify a given group of order n with an isomorphism type in the AllSOTGroups(n) list.
## This is achieved using various group invariants, such as the centre of a group, the derived subgroup, the Fitting subgroup, the Frattini subgroup, the structure of the Sylow subgroups, etc,
  ## and application of the results on classification of split extensions. For further details, see [2, Section 3.2].
######################################################
##
## the case of p-groups of order dividing p^4
##
SOTRec.IdPGroup := function(group, n, fac)
local p, k, i, Id, flag, a, b, c, d, F, N, Zen, gens, pcgs, G, m, x, y;
    p := fac[1][1];
    k := fac[1][2];
    Assert(1, IsPrimeInt(p));
##
    flag := [Exponent(group)];

    if k = 1 then
        return [n, 1];
    fi;

    if k = 2 then
        if flag[1] = n then
            return [n, 1];
        else
            return [n, 2];
        fi;
    fi;

    if k = 3 then
        if IsAbelian(group) then
            if flag[1] = n then
                return [n, 1];
            elif flag[1] = p^2 then
                return [n, 2];
            else
                return [n, 3];
            fi;
        elif flag[1] = p and p > 2 then
            return [n, 4];
        elif flag[1] > p and p > 2 then
            return [n, 5];
        elif p = 2 and Size(Omega(group, 2)) = 8 then
            return [8, 4];
        elif p = 2 and Size(Omega(group, 2)) = 2 then
            return [8, 5];
        fi;
    fi;

    if k = 4 and p > 2 then
        F := FrattiniSubgroup(group);
        Zen := Centre(group);

      if IsAbelian(group) then
          Add(flag, Size(F));
          if flag[1] = n then
              return [n, 1];
          elif flag[1] = p^3 then
              return [n, 2];
          elif flag = [p^2, p^2] then
              return [n, 3];
          elif flag = [p^2, p] then
              return [n, 4];
          else
              return [n, 5];
          fi;
      else
          Append(flag, [IsPowerfulPGroup(group), Size(Zen), IsAbelian(DerivedSubgroup(group)), Exponent(group/DerivedSubgroup(group)), Exponent(Zen)]);
          if flag = [p^2, true, p^2, true, p, p^2] then
              return [n, 6];
          elif flag = [p^3, true, p^2, true, p^2, p^2] then
              return [n, 7];
          elif flag = [p^2, true, p^2, true, p, p] then
              return [n, 8];
          elif flag = [p^2, false, p^2, true, p^2, p] then
              return [n, 9];
          elif flag = [p^2, true, p^2, true, p^2, p] then
              return [n, 10];
          elif flag = [p, false, p^2, true, p, p] then
              return [n, 11];
          elif flag = [p, false, p, true, p, p] then
              return [n, 14];
          elif flag = [p^2, false, p, true, p, p] and p > 3 then
              d := Filtered(Pcgs(F), x -> not x in Zen)[1];
              N := Centralizer(group, F);
              if Exponent(N) = p then
                  return [n, 15];
              else
                  gens := Pcgs(group);
                  a := Filtered(gens, x-> not x in N)[1];
                  b := Filtered(Pcgs(N), x->Order(x) = p^2 and x^p in Zen)[1];
                  pcgs := [a, b, b^p, d];
                  G := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
                  x := Inverse(ExponentsOfPcElement(G, pcgs[2]^pcgs[1])[4]) mod p;
                  y := ExponentsOfPcElement(G, pcgs[4]^(pcgs[1]^x))[3];
                  if Legendre(y, p) = 1 then
                      return [n, 12];
                  else
                      return [n, 13];
                  fi;
              fi;
          elif flag = [9, false, 3, true, 3, 3] then
              if IsAbelian(Omega(group, 3)) then
                  return [81, 15];
              else
                  m := Size(Filtered(group, x -> Order(x) < 4));
                  if m = 27 then
                      return [81, 12];
                  elif m = 63 then
                      return [81, 13];
                  elif m = 45 then
                      return [81, 14];
                  fi;
              fi;
          fi;
      fi;
    elif k = 4 and p = 2 then
        if IsAbelian(group) then
            Add(flag, Size(Agemo(group, 2)));
            if flag[1] = 16 then
                return [16, 1];
            elif flag[1] = 8 then
                return [16, 2];
            elif flag = [4, 4] then
                return [16, 3];
            elif flag = [4, 2] then
                return [16, 4];
            else
                return [16, 5];
            fi;
        else
            Zen := Centre(group);
            flag := [Exponent(Zen), Size(Agemo(group, 2)), Size(Zen), Size(Omega(group, 2))];
            if flag{[1, 2]} = [4, 2] then
                return [16, 6];
            elif flag{[1, 2]} = [4, 4] then
                return [16, 11];
            elif flag{[1, 2, 3, 4]} = [2, 2, 4, 16] then
                return [16, 7];
            elif flag{[1, 2, 3, 4]} = [2, 4, 4, 8] then
                return [16, 8];
            elif flag{[1, 2, 3, 4]} = [2, 2, 4, 4] then
                return [16, 9];
            elif flag{[1, 2, 3, 4]} = [2, 4, 4, 4] then
                return [16, 10];
            elif flag{[3, 4]} = [2, 8] then
                return [16, 12];
            elif flag{[3, 4]} = [2, 16] then
                return [16, 13];
            else
                return [16, 14];
            fi;
        fi;
    fi;
end;

######################################################
#
# the case of groups of order pq
#
SOTRec.IdGroupPQ := function(group, n, fac)
local p, q, Id;
    q := fac[1][1];
    p := fac[2][1];
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    if not (p - 1) mod q = 0 and IsAbelian(group) then
        return [n, 1];
    elif IsAbelian(group) then
        return [n, 2];
    else
        return [n, 1];
    fi;
end;
######################################################
#
# the case of groups of order p^2q
#
SOTRec.IdGroupP2Q := function(group, n, fac)
local p, q, Id, a, b, c, d, flag, P, Q, Zen,gens, G, exps1, exps2, pcgs, pc, m, det, x, k, pcgsp, pcgsq;
    p := fac[2][1];
    q := fac[1][1];
    ####
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    a := Z(p);
    b := Z(q);
    c := ZmodnZObj(Int(Z(p)),p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c;
    else
      d := c + 1;
    fi;
    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    pcgsp := Pcgs(P);
    pcgsq := Pcgs(Q);
    Zen := Centre(group);

    flag := [Exponent(P), Size(Zen)];

    if IsAbelian(group) then
      if flag[1] = p^2 then
        return [n, 1];
      else
        return [n, 2];
      fi;
    elif p > q and q > 2 and (p + 1) mod q = 0 then
      if flag[1] = p then
        return [n, 3];
      fi;
    elif (p - 1) mod q = 0 and q > 2 then
      if flag{[1, 2]} = [p, p] then
        return [n, 3];
      elif flag{[1, 2]} = [p, 1] then
        gens := [pcgsq[1], pcgsp[1], pcgsp[2]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exps1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exps2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        m := [ exps1{[2, 3]}, exps2{[2, 3]} ] * One(GF(p));
        x := Inverse(LogFFE(Eigenvalues(GF(p), m)[1], a^((p - 1)/q))) mod q;
        det := LogFFE((LogFFE(DeterminantMat(m^x), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        if det < (q + 1)/2 then
          k := det;
        else
          k := (q - 1) - det;
        fi;
        return [n, 4 + k];
      elif flag[1] = p^2 then
        return [n, 5 + (q - 1)/2];
      fi;
    elif p > q and q = 2 then
      if flag{[1, 2]} = [p, p] then
        return [n, 3];
      elif flag{[1, 2]} = [p, 1] then
        return [n, 4];
      elif flag[1] = p^2 then
        return [n, 5];
      fi;
    elif p = 2 and q = 3 then
      if flag[1] = p^2 then
        return [12, 5];
      elif flag[2] = 2 then
        return [12, 4];
      else
        return [12, 3];
      fi;
    elif (q - 1) mod p = 0 and q > 3 then
      if flag[1] = p then
        return [n, 3];
      elif flag[1] = p^2 then
        if flag[2] = p then
          return [n, 4];
        else
          return [n, 5];
        fi;
      fi;
    fi;
end;
######################################################
#
# the case of groups of order pqr
#
SOTRec.IdGroupPQR := function(group, n, fac)
local p, q, r, a, b, k, G, Q, R, P, flag, c1, c2, c3, c4, c5, pcgs, pcp, pc, x, pcgsp, pcgsq, pcgsr;
    r := fac[1][1];
    q := fac[2][1];
    p := fac[3][1];
    ####
    Assert(1, p > q and q > r);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));

    a := Z(p);
    b := Z(q);

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);
    pcgsp := Pcgs(P);
    pcgsq := Pcgs(Q);
    pcgsr := Pcgs(R);

    c1 := SOTRec.w((q - 1), r);
    c2 := SOTRec.w((p - 1), r);
    c3 := SOTRec.w((p - 1), q);
    c4 := (r - 1)*SOTRec.w((q - 1), r) * SOTRec.w((p - 1), r);
    c5 := SOTRec.w((p - 1), q*r);

    if IsAbelian(group) then
      return [n, 1];
    else
      flag := [Size(Centre(group))];
      if flag[1] = p then
        return [n, 2]; ##r | (q - 1)
      elif flag[1] = q then
        return [n, 2 + c1]; ##r |(p - 1)
      elif (p - 1) mod q = 0 and flag[1] = r then
        return [n, 2 + c1 + c2];
      elif flag[1] = 1 then
        if pcgsp[1]^pcgsq[1] = pcgsp[1] and (q - 1) mod r = 0 and (p - 1) mod r = 0 then ##r |(p - 1) and r | (q - 1)
          pcgs := [pcgsr[1], pcgsq[1], pcgsp[1]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2]*One(GF(q)), b^((q-1)/r))) mod r;
          k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^(pcgs[1]^x))[3]*One(GF(p)), a^((p-1)/r)) mod r;
          return [n, 3 + c3 + k];
        elif pcgsp[1]^pcgsq[1] <> pcgsp[1] and (p - 1) mod (r*q) = 0 then
          return [n, 2 + c1 + c2 + c3 + c4];
        fi;
      fi;
    fi;
end;
######################################################
######################################################
######################################################
#
# the case of groups of order p^2q^2
#
SOTRec.IdGroupP2Q2 := function(group, n, fac)
local p, q, P, Q, Zen,a, b, c, d, e, f, ind, gens, G, pcgs, pc, g, h, ev,
  gexp1, gexp2, gexp3, gexp4, mat, Id, k, l, x, y, det, mat1, mat2, pcgsp, pcgsq;
    q := fac[1][1];
    p := fac[2][1];
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    Q := SylowSubgroup(group, q);
    P := SylowSubgroup(group, p);
    Zen := Centre(group);

    pcgsp := Pcgs(P);
    pcgsq := Pcgs(Q);
    a := Z(p);
    b := Z(q);
    c := ZmodnZObj(Int(Z(p)), p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c;
    else
      d := c + 1;
    fi;
    e := ZmodnZObj(Int(Z(q)), q^2);
    if not e^(q - 1) = ZmodnZObj(1, q^2) then
      f := e;
    else
      f := e + 1;
    fi;

    ind := [Exponent(P), Exponent(Q)];

    if IsAbelian(group) then
        if ind[1] = p^2 and ind[2] = q^2 then
          return [n, 1];
        elif ind[2] = q^2 then
          return [n, 2];
        elif ind[1] = p^2 then
          return [n, 3];
        else
          return [n, 4];
        fi;
    else
        gens := [];
        Append(gens, Filtered(pcgsq, x-> not x in Zen));
        Append(gens, Filtered(pcgsq, x-> not x in gens));
        Append(gens, pcgsp);
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
        Add(ind, Size(Zen));
    fi;

    if n = 36 then
        k := Position([ [ 9, 4, 36 ], [ 3, 4, 36 ], [ 9, 2, 36 ], [ 3, 2, 36 ], [ 9, 4, 2 ], [ 9, 2, 2 ], [ 9, 2, 3 ], [ 3, 4, 6 ], [ 3, 4, 2 ], [ 3, 4, 1 ], [ 3, 2, 6 ], [ 3, 2, 2 ], [ 3, 2, 1 ], [ 3, 2, 3 ] ], ind);
        return [36, k];
    fi;
    if ((p - 1) mod q = 0 and q > 2) then
        if ind = [p^2, q^2, q] then
            return [n, 5];
        elif ind = [p^2, q^2, 1] and ((p - 1) mod q^2 = 0 and q > 2) then
            return [n, 5 + SOTRec.w((p - 1), q^2)];
        elif ind = [p^2, q, q] then
            return [n, 6 + SOTRec.w((p - 1), q^2)];
        elif ind = [p, q^2, q*p] then
            return [n, 7 + SOTRec.w((p - 1), q^2)];
        elif ind = [p, q^2, q] then
            g := Filtered(pcgsq, x -> Order(x) = q^2)[1];
            gens := [g, g^q, pcgsp[1], pcgsp[2]];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            mat := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
            x := Inverse(LogFFE(Eigenvalues(GF(p), mat)[1], a^((p - 1)/q))) mod q;
            det := LogFFE((LogFFE(DeterminantMat(mat^x), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
            if det < (q + 1)/2 then
                k := det;
            else
                k := (q - 1) - det;
            fi;
            return [n, 6 + 2 + k + SOTRec.w((p - 1), q^2)];
        elif ind = [p, q^2, p] and (p - 1) mod (q^2) = 0 and q > 2 then
            return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2)];
        elif ind = [p, q^2, 1] and (p - 1) mod (q^2) = 0 and q > 2 then
            g := Filtered(pcgsq, x -> Order(x)=q^2)[1];
            h := Filtered(pcgsp, x -> not x in Centre(Group([g^q, pcgsp[1], pcgsp[2]])))[1];
            if Size(Centre(Group([g^q, pcgsp[1], pcgsp[2]]))) = p then
                gens := [g, g^q, h, Pcgs(Centre(Group([g^q, pcgsp[1], pcgsp[2]])))[1]];
                G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
                gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
                gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
                mat := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
                x := Inverse(LogFFE(Filtered(Eigenvalues(GF(p), mat), x -> Order(x) = q^2)[1], a^((p - 1)/(q^2)))) mod q^2;
                ev := List(Eigenvalues(GF(p), mat^x), x -> LogFFE(x, a^((p - 1)/(q^2))));
                k := Filtered(ev, x -> x <> 1)[1]/q;
                return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2) + (q^2 - q + 2)/2 + k];
            else
                gens := [g, g^q, h, Filtered(pcgsp, x -> x <> h)[1]];
                G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
                gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
                gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
                mat := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
                x := Inverse(LogFFE(Eigenvalues(GF(p), mat)[1], a^((p - 1)/(q^2)))) mod q^2;
                ev := List(Eigenvalues(GF(p), mat^x), x -> LogMod(LogFFE(x, a^((p - 1)/(q^2))), Int(f), q^2) mod (q^2 - q));
                if Length(ev) = 1 then
                    k := 0;
                    return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2) + k + 1];
                elif Length(ev) > 1 then
                    k := Filtered(ev, x -> x <> 0)[1];
                    if k > (q^2 - q)/2 then
                        return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2) + (q^2 - q - k) + 1];
                    else
                        return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2) + k + 1];
                    fi;
                fi;
            fi;
        elif ind = [p, q, q * p] and q > 2 then
            return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2)*(q^2 + q + 4)/2 ];
        elif ind = [p, q, q] and q > 2 then
            g := Filtered(pcgsq, x -> not x in Zen)[1];
            h := Pcgs(Zen)[1];
            gens := [g, h, pcgsp[1], pcgsp[2]];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            mat := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
            x := Inverse(LogFFE(Eigenvalues(GF(p), mat)[1], a^((p - 1)/q))) mod q;
            det := LogFFE((LogFFE(DeterminantMat(mat^x), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
            if det < (q + 1)/2 then
                k := det;
            else
                k := (q - 1) - det;
            fi;
            return [n, 6 + (q + 5)/2 + SOTRec.w((p - 1), q^2)*(q^2 + q + 4)/2 + k + 1];
        elif ind = [p, q, 1] and q > 2 then
            return [n, 10 + q + SOTRec.w((p - 1), q^2)*(q^2 + q + 4)/2];
        fi;
    fi;
    if (p + 1) mod q = 0 and q > 2 then
        if ind = [p, q, q] then
            return [n, 6 + SOTRec.w((p + 1), q^2)];
        elif ind = [p, q^2, q] then
            return [n, 5];
        fi;
    fi;
    if ( p + 1) mod (q^2) = 0 and q > 2 and ind[3] = 1 then
        return [n, 6];
    fi;

    if q = 2 and p > 3 then
        if ind = [p^2, 4, 2] then
            return [n, 5];
        elif p mod 4 = 1 and ind = [p^2, 4, 1] then
            return [n, 5 + SOTRec.w((p - 1), 4)];
        elif ind{[1, 2]} = [p^2, 2] then
            return [n, 6 + SOTRec.w((p - 1), 4)];
        elif ind = [p, 4, 2*p] then
            return [n, 7 + SOTRec.w((p - 1), 4)];
        elif ind = [p, 4, 2] then
            return [n, 8 + SOTRec.w((p - 1), 4)];
        elif p mod 4 = 1 and ind = [p, 4, p] then
            return [n, 8 + 1 + SOTRec.w((p - 1), 4)];
        elif p mod 4 = 1 and ind = [p, 4, 1] then
            gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            gexp3 := ExponentsOfPcElement(G, gens[3]^gens[2]);
            gexp4 := ExponentsOfPcElement(G, gens[4]^gens[2]);
            mat1 := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
            mat2 := [gexp3{[3, 4]}, gexp4{[3, 4]}]*One(GF(p));
            x := DeterminantMat(mat1);
            y := DeterminantMat(mat2);
            if AsSet([Int(x), Int(y)]) = AsSet([p - 1, 1]) then
                return [n, 8 + 2 + SOTRec.w((p - 1), 4)];
            elif AsSet([Int(x), Int(y)]) = AsSet([1, 1]) then
                return [n, 8 + 3 + SOTRec.w((p - 1), 4)];
            elif (not a^0 in Eigenvalues(GF(p), mat1) and a^0 in Eigenvalues(GF(p), mat2)) or (not a^0 in Eigenvalues(GF(p), mat2) and a^0 in Eigenvalues(GF(p), mat1)) then
                return [n, 8 + 4 + SOTRec.w((p - 1), 4)];
            fi;
        elif p mod 4 = 3 and ind = [p, q^2, 1] then
            return [n, 9];
        elif ind = [p, q, 2 * p] then
            return [n, 9 + SOTRec.w((p + 1), 4)+ 5*SOTRec.w((p - 1), 4)];
        elif ind = [p, q, 2] then
            return [n, 10 + SOTRec.w((p + 1), 4)+ 5*SOTRec.w((p - 1), 4)];
        elif ind = [p, q, 1] then
            return [n, 11 + SOTRec.w((p + 1), 4)+ 5*SOTRec.w((p - 1), 4)];
        fi;
    fi;
end;
######################################################
#
# the case of groups of order p^3q
#
SOTRec.IdGroupP3Q := function(group, n, fac)
local p, q, P, Q, O, Zen, a, b, r1, r2, r3, s1, s2, s3, c, d, e, f, g, h, x, y, k, l, tst,
  Id, gens, pc, pcgs, G, exp1, exp2, exp3, mat, matGL2, matGL3, det, Idfunc, tmp, ev, evm, N1, N2,
  c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, pcgsp, pcgsq;
    p := fac[2][1];
    q := fac[1][1];
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ##
    Idfunc := function(q, l)
      local x, y, a, b, tuple, n, id;
        x := l[1] mod (q - 1);
        y := l[2] mod (q - 1);
        if l in [[(q-1)/3, 2*(q-1)/3], [2*(q-1)/3, (q-1)/3]] then
          return 1/6*(q^2 - 5*q + 6 + 4*SOTRec.w((q - 1), 3));
        else
          tuple := SortedList(Filtered(
          [SortedList([x, y]), SortedList([-x, y-x] mod (q - 1)), SortedList([-y, x-y] mod (q - 1))],
          list -> list[1] < Int((q + 2)/3) and list[2] < q - 1 - list[1]))[1];
          a := tuple[1];
          b := tuple[2];
          return Sum([1..a-1], x -> q - 1 - 3*x) + b + 1 - 2*a;
        fi;
    end;
    ##
    a := Z(p);
    b := Z(q);
    if (q - 1) mod p = 0 then
      r1 := b^((q-1)/p);
    fi;
    if (q - 1) mod (p^2) = 0 then
      r2 := b^((q-1)/(p^2));
    fi;
    if (q - 1) mod (p^3) = 0 then
      r3 := b^((q-1)/(p^3));
    fi;
    P := SylowSubgroup(group, p);
    pcgsp := Pcgs(P);
    Q := SylowSubgroup(group, q);
    pcgsq := Pcgs(Q);
    Zen := Centre(group);

    tst := [IsNormal(group, P), IsNormal(group, Q), IsAbelian(P), Exponent(P), Size(Zen)];
    if p = 2 then
      Add(tst, Size(Omega(P, 2)));
    fi;
  ############ enumeration
    c1 := SOTRec.delta(n, 24) + SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3);
    c2 := 2*SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c3 := SOTRec.w((q - 1), p);
    c4 := SOTRec.w((q - 1), p) + SOTRec.delta(p, 2);
    c5 := p*SOTRec.w((q - 1), p)*(1 - SOTRec.delta(p, 2)) + SOTRec.delta(p, 2);
    c6 := SOTRec.w((p - 1), q);
    c7 := (q + 1)*SOTRec.w((p - 1), q);
    c8 := (1 - SOTRec.delta(q, 2))*(
    1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3))*SOTRec.w((p - 1), q)
    + SOTRec.w((p^2 + p + 1), q)*(1 - SOTRec.delta(q, 3))
    + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2)))
    + 3*SOTRec.delta(q, 2);
    c9 := (1/2*(q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(q, 2))*(1 - SOTRec.delta(p, 2))
    + 2*SOTRec.delta(q, 2);
    c10 := SOTRec.w((p - 1), q);
  ############ abelian groups:
    if IsAbelian(group) then
      if tst[4] = p^3 then
        return [n, 1];
      elif tst[4] = p^2 then
        return [n, 2];
      elif tst[4] = p then
        return [n, 3];
      fi;
    fi;
  ############ case 1: no normal Sylow subgroup -- necessarily n = 24
    if not IsNormal(group, P) and not IsNormal(group, Q) then
      return [24, 15];
    fi;
  ############ interlude: n = 24
    if n = 24 and not IsAbelian(group) then
      if [tst[1], tst[2], tst[4], tst[6]] = [ true, true, 4, 8 ] then
        return [24, 4];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, true, 4, 2 ] then
        return [24, 5];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 8, 2 ] then
        return [24, 6];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 4 ] then
        O := Omega(P, 2);
        if IsNormal(group, O) then
          return [24, 8];
        else
          return [24, 7];
        fi;
      elif [tst[1], tst[2], tst[4], tst[6], tst[5]] = [ false, true, 2, 8, 4 ] then
        return [24, 9];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 8 ] then
        d := pcgsq[1];
        repeat c := Random(P); until not c in Centre(P) and d*c = c*d;
        O := Group([c, d, Pcgs(Zen)[1]]);
        if IsCyclic(O) then
          return [24, 11];
        else
          return [24, 10];
        fi;
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 2 ] then
        return [24, 12];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, false, 2, 8 ] then
        return [24, 13];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, false, 4, 2 ] then
        return [24, 14];
      fi;
    fi;

  ############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
    if p > 2 and [tst[1], tst[2]] = [true, true] and IsAbelian(group) = false then
      if tst[4] = p then
        return [n, 4];
      elif tst[4] = p^2 then
        return [n, 5];
      fi;
    elif p = 2 and q > 3 and IsNilpotent(group) and IsAbelian(group) = false then
      if tst[6] = 8 then
        return [n, 4];
      elif tst[6] = 2 then
        return [n, 5];
      fi;
    fi;

  ############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
    if n <> 24 and [tst[1], tst[2]] = [false, true] then ##it follows that (q - 1) mod p = 0
      ## class 1: when P = C_{p^3}
      if tst[4] = p^3 and (q - 1) mod p = 0 then
        if tst[5] = p^2 then
          return [n, 6];
        elif (q - 1) mod (p^2) = 0 and tst[5] = p then
          return [n, 7];
        elif (q - 1) mod (p^3) = 0 and tst[5] = 1 then
          return [n, 8];
        fi;
      ## class 2: when P = C_{p^2} \times C_p, there are at most three isom types of semidirect products of P \ltimes Q
      elif tst[3] = true and tst[4] = p^2 then
        if Exponent(Zen) = p^2 then
          return [n, 6 + c1];
        elif Exponent(Zen) = p and tst[5] = p^2 then
          return [n, 7 + c1];
        elif (q - 1) mod (p^2) = 0 and tst[5] = p then
          return [n, 8 + c1];
        fi;
      ## class 3: when P is elementary abelian, there is at most one isom type of P \ltimes Q
      elif tst[3] = true and (q - 1) mod p = 0 then
        return [n, 6 + c1 + c2];
      ## class 4: when P is extraspecial + type
      elif not tst[3] = true and tst[4] = p and p > 2 then
        return [n, 6 + c1 + c2 + c3];
      elif not tst[3] = true and tst[4] = 4 and tst[6] = 8 then
        d := pcgsq[1];
        repeat c := Random(P); until not c in Centre(P) and d*c = c*d;
        O := Group([c, d, Pcgs(Zen)[1]]);
        if IsCyclic(O) then
          return [n, 11 + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3)];
        else
          return [n, 10 + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3)];
        fi;
      ## class 5: when P is extraspecial - type
      elif not tst[3] = true and tst[4] = p^2 and p > 2 then
        repeat c := Random(P); until Order(c) = p and not c in Centre(P) and not IsCyclic(Group([c, Pcgs(Centre(P))[1]]));
        d := pcgsq[1];
        repeat g := Random(P); until Order(g) = p^2 and g^p in Centre(P);
        h := g^p;
        gens := [c, g, h, d];;
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
        x := Inverse(ExponentsOfPcElement(G, gens[2]^gens[1])[3]) mod p;
        k := LogFFE(ExponentsOfPcElement(G, gens[4]^(gens[1]^x))[4]*One(GF(q)), r1) mod p;
        if k > 0 then
          return [n, 10 + k + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3)];
        else
          return [n, 11 + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3) + (p - 1)];
        fi;
      ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
      elif not tst[3] = true and tst[6] = 2 then
        return [n, 12 + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3)];
      fi;
    fi;
  ############ case 4: nonabelian and only the Sylow p-subgroup is normal
    if n <> 24 and [tst[1], tst[2]] = [true, false] then
      if (p - 1) mod q = 0 then
        s1 := a^((p - 1)/q);

        c := ZmodnZObj(Int(Z(p)), p^3);
        if not c^(p - 1) = ZmodnZObj(1, p^2) then
          d := c;
        else
          d := c + 1;
        fi;
        s3 := d^((p^3 - p^2)/q);

        e := ZmodnZObj(Int(Z(p)), p^2);
        if not e^(p - 1) = ZmodnZObj(1, p^2) then
          f := e;
        else
          f := e + 1;
        fi;

        s2 := f^((p^2-p)/q);
      fi;

      ## class 1: when P is cyclic, there is at most isom type of semidirect products of Q \ltimes P #it follows that (p - 1) mod q = 0
      if tst[4] = p^3 then
        return [n, 6];
      ## class 2: when P = C_{p^2} \times C_p, there are at most (q + 1) isomorphism types of Q \ltimes P
    elif tst[3] = true and tst[4] = p^2 and tst[5] = p^2 then ## (C_q \ltimes C_p) \times C_{p^2}
        return [n, 7];
      elif tst[3] = true and tst[4] = p^2 and tst[5] = p then ## (C_q \ltimes C_{p^2}) \times C_p
        return [n, 8];
      elif tst[3] = true and tst[4] = p^2 and tst[5] = 1 and q > 2 then ## C_q \ltimes (C_{p^2} \times C_p)
        repeat g := Random(P); until Order(g) = p and not g in FrattiniSubgroup(P);
        h := Filtered(pcgsp, x -> Order(x) = p^2)[1];
        gens:= [pcgsq[1], h, h^p, g];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        x := Inverse(LogMod(ExponentsOfPcElement(G, gens[3]^gens[1])[3], Int(s2), p)) mod q;
        k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(p)), s1) mod q;
        return [n, 8 + k];
      elif tst[3] = true and tst[4] = p^2 and tst[5] = 1 and q = 2 then ## C_q \ltimes (C_{p^2} \times C_p)
        return [n, 9];
      ## class 3: when P is elementary abelian
    elif tst[3] = true and tst[5] = p^2 then ## (C_q \ltimes C_p) \times C_p^2
        return [n, 9 + (q - 1)];
      elif tst[3] = true and tst[5] = p and (p - 1) mod q = 0 and q > 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
        gens:= [pcgsq[1], Filtered(pcgsp, x->not x in Zen)[1], Filtered(pcgsp, x->not x in Zen)[2], Filtered(pcgsp, x->x in Zen)[1]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}]* One(GF(p));
        x := Inverse(LogFFE(Eigenvalues(GF(p), matGL2)[1], s1)) mod q;
        det := LogFFE((LogFFE(DeterminantMat(matGL2^x), s1) - 1)*One(GF(q)), b) mod (q - 1);
        if det < (q + 1)/2 then
          k := det;
        else
          k := (q - 1) - det;
        fi;
        return [n, 10 + k + (q - 1)];
      elif tst[3] = true and tst[5] = p and q = 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
        return [n, 10 + (q - 1)];
      elif tst[3] = true and tst[5] = p and (p + 1) mod q = 0 and q > 2 then
        return [n, 6 + (5 + p)*SOTRec.w((q - 1), p)];
      ## below: (C_q \ltimes C_p^3) when q | (p - 1)
      elif tst[3] = true and tst[5] = 1 and q = 2 then
        return [n, 12];
      elif tst[3] = true and tst[5] = 1 and (p - 1) mod q = 0 and q > 2 then
        gens := [pcgsq[1], pcgsp[1], pcgsp[2], pcgsp[3]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        mat := [exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p));
        ev := Eigenvalues(GF(p), mat);
        if Length(ev) = 1 then
          return [n, 10 + (q + 1)/2 + (q - 1)];
        elif Length(ev) <> 1 then
          if Length(ev) = 2 then
            evm := SOTRec.EigenvaluesWithMultiplicitiesGL3P(mat, p);
            x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
            k := LogFFE(Filtered(evm, x -> x[2] = 1)[1][1]^x, s1) mod q;
            return [n, 9 + k + (q + 1)/2 + (q - 1)];
          elif Length(ev) = 3 then
            x := Inverse(LogFFE(Eigenvalues(GF(p), mat)[1], s1)) mod q;
            l := List(ev, i -> i^x);
            y := List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q)));
            l := List(y, x -> (LogFFE(x, b) mod (q - 1)));
            k := Idfunc(q, l);
            return [n, 9 + k + (q - 1) + (q + 1)/2 + (q - 1)];
          fi;
        fi;
      elif tst[3] = true and tst[4] = p and tst[5] = 1 and (p^2 + p + 1) mod q = 0 and q > 3 then
        return [n, 5 + (5+p)*SOTRec.w((q-1), p) + 2*SOTRec.w((q-1), p^2)
          + SOTRec.w((q-1), p^3) + (15+q^2+10*q+4*SOTRec.w((q-1),3))*SOTRec.w((p-1), q)*(1 - SOTRec.delta(q, 2))/6
          + SOTRec.w((p+1), q) + SOTRec.w((p^2+p+1), q)*(1 - SOTRec.delta(q, 3))];
      ## class 4: when P is extraspecial of type +
      elif (not tst[3] = true and tst[4] = p and (p - 1) mod q = 0) then
        if tst[5] = p then ## q | (p - 1), Z(G) = C_p
          if n mod 2 = 1 then
            return [n, 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8];
          else
            return [n, 5 + 7*SOTRec.delta(p, 2) + 2*SOTRec.w((q-1),4) + SOTRec.w((q-1), 8)
            + 8*SOTRec.delta(q, 2) + 3*SOTRec.delta(n,24) + SOTRec.delta(n, 56)];
          fi;
        elif tst[5] = 1 then ## q | (p - 1), Z(G) = 1
          if Size(DerivedSubgroup(group)) = p^2 and q > 2 then
            return [n, 8 + (15+q^2+10*q+4*SOTRec.w((q-1),3))/6 + SOTRec.w((p^2+p+1), q)*(1 - SOTRec.delta(q, 3))];
          elif Size(DerivedSubgroup(group)) = p^2 and q = 2 then
            return [n, 5 + 7*SOTRec.delta(p,2) + 2*SOTRec.w((q-1),4) + SOTRec.w((q-1), 8)
              + 9*SOTRec.delta(q, 2) + 3*SOTRec.delta(n,24) + SOTRec.delta(n, 56)];
          elif Size(DerivedSubgroup(group)) = p^3 and q > 2 then
            gens := [pcgsq[1], Filtered(pcgsp, x -> not x in Centre(P))[1], Filtered(pcgsp, x -> not x in Centre(P))[2], Filtered(pcgsp, x->x in Centre(P))[1]];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            x := Inverse(LogFFE(exp3[4] * One(GF(p)), s1)) mod q;
            matGL3 := ([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}])^x * One(GF(p));
            y := List(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1), x -> LogFFE(x, s1) mod q)[1];
            if y > (q + 1)/2 then
              k := (q + 1) - y - 1;
            else
              k := y - 1;
            fi;
            return [n, 8 + k + (15+q^2+10*q+4*SOTRec.w((q-1),3))/6 + SOTRec.w((p^2+p+1), q)*(1 - SOTRec.delta(q, 3))];
          fi;
        fi;
      elif not tst[3] = true and tst[4] = p and (p + 1) mod q = 0 and q > 2 and p > 2 then
        return [n, 7];
      ## class 5: when P is extraspecial of type -,
      elif not tst[3] = true and tst[4] = p^2 and (p - 1) mod q = 0 then
        if n mod 2 = 1 then
          return [n, 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9];
        else
          return [n, 5 + 7*SOTRec.delta(p, 2) + 2*SOTRec.w((q-1),4) + SOTRec.w((q-1), 8)
            + 10*SOTRec.delta(q, 2) + 3*SOTRec.delta(n,24) + SOTRec.delta(n, 56)];
        fi;
      fi;
    fi;
end;
######################################################
#
# the case of groups of order p^2qr
#
SOTRec.IdGroupP2QR := function(group, n, fac)
local p, q, r, P, Q, R, Zen,a, b, c, u, v, flag, G, gens, pc, pcgs, g, h,
  c1, c2, c3, c4, c5, c6, c7, k, l, m, tmp, exp, exp1, exp2, expp1q, expp2q, expp1r, expp2r,
  matq, det, matr, detr, matqr, evqr, mat, mat_k, Id, x, y, z, ev, lst, N1, N2,
  pcgsp, pcgsq, pcgsr;

    p := fac[3][1];
    q := fac[1][1];
    r := fac[2][1];
    ####
    Assert(1, r > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));

    a := Z(r);;
    b := Z(p);;
    c := Z(q);;

    u := ZmodnZObj(Int(Z(p)), p^2);;
    if not u^(p-1) = ZmodnZObj(1, p^2) then
      v := u;
    else
      v := u + 1;
    fi;

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);
    pcgsp := Pcgs(P);
    pcgsq := Pcgs(Q);
    pcgsr := Pcgs(R);
    Zen := Centre(group);

    flag := [Size(FittingSubgroup(group)), Size(Zen), Exponent(P)];

    c1 := SOTRec.w((r - 1), p^2*q);;
    c2 := SOTRec.w((q - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
    + (p^2 - p)*SOTRec.w((r - 1), p^2)*SOTRec.w((q - 1), p^2)
    + SOTRec.w((r - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p^2)
    + SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p);;
    c3 := 1/2*(q*r+q+r+7)*SOTRec.w((p - 1), q*r)
    + SOTRec.w((p^2 - 1), q*r)*(1 - SOTRec.w((p - 1), q*r))*(1 - SOTRec.delta(q, 2))
    + 2*SOTRec.w((p + 1), r)*SOTRec.delta(q, 2);;
    c4 := 1/2*(r + 5)*SOTRec.w((p - 1), r) + SOTRec.w((p + 1), r);;
    c5 := 8*SOTRec.delta(q, 2)
    + (1 - SOTRec.delta(q, 2))*(1/2*(q - 1)*(q + 4)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
    + 1/2*(q - 1)*SOTRec.w((p + 1), q)*SOTRec.w((r - 1), q)
    + 1/2*(q + 5)*SOTRec.w((p - 1), q)
    + 2*SOTRec.w((r - 1), q)
    + SOTRec.w((p + 1), q));;
    c6 := SOTRec.w((r - 1), p)*(SOTRec.w((p - 1), q)*(1 + (q - 1)*SOTRec.w((r - 1), q))
    + 2*SOTRec.w((r - 1), q));;
    c7 := 2*(SOTRec.w((q - 1), p) + SOTRec.w((r - 1), p) +
    (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)) + SOTRec.delta(n, 60);

    if IsSolvable(group) then
      ############ abelian groups:
      if IsAbelian(group) and flag[3] = p^2 then
        return [n, 1];
      elif IsAbelian(group) and flag[3] = p then
        return [n, 2];
      fi;
      ############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
      if flag[1] = r then
        return [n, 3]; ##C_{p^2q} \ltimes C_r
      ############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or (p^2 | (q - 1) or (r - 1)) or (p | (q - 1) and p | (r - 1))
      elif flag[1] = q*r then
        if flag[2] = r then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          return [n, 3 + c1];
        elif flag[2] = q then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
          return [n, 3 + c1 + (p^2 - p)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p^2)
          + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
          + SOTRec.w((q - 1), (p^2))];
        elif flag[2] = 1 and flag[3] = p^2 then
          gens := [pcgsp[1], pcgsp[2], pcgsq[1], pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp := ExponentsOfPcElement(G, gens[3]^gens[1]);

          if IsOne(Comm(gens[2], gens[4])) and not IsOne(Comm(gens[2], gens[3])) then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/(p^2)))) mod (p^2);
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
            k := LogFFE(exp1[4]*One(GF(r)), a^((r-1)/p)) mod p;
            return [n, 2 + k + c1 + SOTRec.w((q - 1), (p^2))];
          elif (not IsOne(Comm(gens[2], gens[4]))) and (not IsOne(Comm(gens[2], gens[3]))) then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/(p^2)))) mod (p^2);
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
            k := PositionSet(SOTRec.groupofunitsP2(p), LogFFE(exp1[4]*One(GF(r)), a^((r-1)/(p^2))) mod (p^2));
            return [n, 2 + k + c1 + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
            + SOTRec.w((q - 1), (p^2))];
          elif (not IsOne(Comm(gens[2], gens[4]))) and IsOne(Comm(gens[2], gens[3])) then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/p))) mod p;
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
            k := LogFFE(exp1[4]*One(GF(r)), a^((r-1)/p)) mod p;
            return [n, 2 + k + c1 + SOTRec.w((r - 1), p^2) + (p^2 - p)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p^2)
            + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
            + SOTRec.w((q - 1), (p^2))];
          fi;
        elif flag[2] = 1 and Exponent(group) = p * q * r then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
          return [n, 3 + c1 + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p^2)
          + SOTRec.w((r - 1), p^2) + (p^2 - p)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p^2)
          + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
          + SOTRec.w((q - 1), (p^2))];
        fi;
      ############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    elif flag[1] = p^2 and flag[3] = p^2 and flag[2] = 1 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
        return [n, 3 + c1 + c2];
      elif flag[1] = p^2 and flag[3] = p and flag[2] = 1 and (p - 1) mod (q*r) = 0 then
        N1 := Group([pcgsq[1], pcgsp[1], pcgsp[2]]);
        N2 := Group([pcgsr[1], pcgsp[1], pcgsp[2]]);
        if Size(Centre(N1)) = p and Size(Centre(N2)) = p then
           return [n, 3 + c1 + c2 + SOTRec.w((p - 1), q*r)];
        elif pcgsr[1]^pcgsq[1] = pcgsr[1] and Size(Centre(N2)) = p and Size(Centre(N1)) = 1 then ##R acts trivially on one of the generators of P
          gens := [pcgsq[1]*pcgsr[1], pcgsq[1], Filtered(pcgsp, x-> x^pcgsq[1] <> x and x^pcgsr[1] <> x)[1], Pcgs(Centre(N2))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat := [exp1{[3, 4]}, exp2{[3, 4]}]*One(GF(p));
          ev := Eigenvalues(GF(p), mat);
          if Length(ev) = 1 then
            k := 1;
          else
            x := Inverse(LogFFE(Filtered(ev, x->Order(x) = q*r)[1], b^((p - 1)/(q*r)))) mod (q*r);
            matq := mat^x;
            k := LogFFE(Filtered(Eigenvalues(GF(p), matq), x->Order(x) = q)[1], b^((p - 1)/(q*r))) mod q;
          fi;
          return [n, 3 + (k - 1) + c1 + c2 + 3*SOTRec.w((p - 1), q*r)];
        elif pcgsr[1]^pcgsq[1] = pcgsr[1] and Size(Centre(N1)) = p and Size(Centre(N2)) = 1 then ##Q acts trivially on one of the generators of P
          gens := [pcgsq[1]*pcgsr[1], pcgsr[1], Filtered(pcgsp, x-> x^pcgsq[1] <> x and x^pcgsr[1] <> x)[1], Pcgs(Centre(N1))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat := [exp1{[3, 4]}, exp2{[3, 4]}]*One(GF(p));
          ev := Eigenvalues(GF(p), mat);
          if Length(ev) = 1 then
            k := 1;
          else
            x := Inverse(LogFFE(Filtered(ev, x->Order(x) = q*r)[1], b^((p - 1)/(q*r)))) mod (q*r);
            matr := mat^x;
            k := LogFFE(Filtered(Eigenvalues(GF(p), matr), x->Order(x) = r)[1], b^((p - 1)/(q*r))) mod r;
          fi;
          return [n, 3 + (k - 1) + c1 + c2
                  + 3*SOTRec.w((p - 1), q*r)
                  + (q - 1) * SOTRec.w((p - 1), q*r)];
        elif pcgsr[1]^pcgsq[1] = pcgsr[1] and Size(Centre(N1)) = 1 and Size(Centre(N2)) = 1 then ## Q and R act nontrivially on both the generators of P
          gens := [pcgsq[1]*pcgsr[1], pcgsr[1], pcgsp[1], pcgsp[2]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat := [exp1{[3, 4]}, exp2{[3, 4]}] * One(GF(p));
          x := Eigenvalues(GF(p), mat);
          if (p-1) mod (q*r) = 0 and q > 2 then
            tmp := [];
            for k in [0..(q - 1)/2] do
              for l in [0..(r - 1)/2] do
                Add(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]])); #AsSet([[(k) mod (q - 1), (-l) mod (r - 1)], [(-k) mod (q - 1), (l) mod (r - 1)]])]));
              od;
            od;
            for k in [1..(q-3)/2] do
              for l in [(r+1)/2..(r-2)] do
                Add(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]])); #AsSet([[(k) mod (q - 1), (-l) mod (r - 1)], [(-k) mod (q - 1), (l) mod (r - 1)]])]));
              od;
            od;
          fi;
          if (p-1) mod (q*r) = 0 and q = 2 then
            tmp := [];
            for l in [0..(r-1)/2] do
              Add(tmp, AsSet([[0, l], [0, (-l) mod (r - 1)]]));
            od;
          fi;
          if Length(x) = 1 then
            k := 0;
            l := 0;
          else
            k := LogFFE(LogFFE(x[2], x[1])*One(GF(q)), c) mod (q - 1);
            l := LogFFE(LogFFE(x[2], x[1])*One(GF(r)), a) mod (r - 1);
          fi;
          m := Position(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]]));
          return [n, 3 + (m - 1) + c1 + c2
          + 3*SOTRec.w((p - 1), q*r)
          + (r - 1 + q - 1) * SOTRec.w((p - 1), q*r)];
        elif q = 2 and pcgsr[1]^pcgsq[1] <> pcgsr[1] then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
          return [n, 3 + c1 + c2
          + 3*SOTRec.w((p - 1), q*r)
          + ((r + 1)/2 + r - 1 + q - 1) * SOTRec.w((p - 1), q*r)];
        fi;
      elif flag[1] = p^2 and flag[3] = p and flag[2] = p then  ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
        return [n, 3 + c1 + c2
        + 2*SOTRec.w((p - 1), q*r)];
      elif flag[1] = p^2 and flag[3] = p and flag[2] = 1 and (p + 1) mod (q*r) = 0 and q > 2 then ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
        return [n, 3 + c1 + c2];
      elif flag[1] = p^2 and flag[3] = p and flag[2] = 1 and (p + 1) mod (q*r) = 0 and q = 2 then
        if IsOne(Comm(pcgsq[1], pcgsr[1])) then ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
          return [n, 3 + c1 + c2];
        else ## qr | (p + 1), q = 2, and G \cong (C_2 \ltimes C_r)\ltimes C_p^2
          return [n, 4 + c1 + c2];
        fi;
      elif flag[1] = p^2 and flag[3] = p and flag[2] = 1 and (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        return [n, 3 + c1 + c2];
      elif flag[1] = p^2 and flag[3] = p and flag[2] = 1 and (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        return [n, 3 + c1 + c2];

      ############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
      elif flag[1] = p^2*q then
        if flag[3] = p^2 and flag[2] = q then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
          return [n, 3 + c1 + c2 + c3];
        elif flag[2] = p*q then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
          return [n, 3 + c1 + c2 + c3
          + SOTRec.w((p - 1), r)];
        elif flag[3] = p and flag[2] = q and (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          gens := [pcgsr[1], pcgsp[1], pcgsp[2], pcgsq[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1r := ExponentsOfPcElement(G, gens[2]^gens[1]);
          expp2r := ExponentsOfPcElement(G, gens[3]^gens[1]);
          matr := [expp1r{[2, 3]}, expp2r{[2, 3]}]*One(GF(p));
          x := Inverse(LogFFE(Eigenvalues(GF(p), matr)[1], b^((p-1)/r))) mod r;
          detr := LogFFE((LogFFE(DeterminantMat(matr^x), b^((p-1)/r)) - 1)*One(GF(r)), a) mod (r - 1);
          if detr < (r + 1)/2 then
            k := detr;
          else
            k := (r - 1) - detr;
          fi;
          return [n, 3 + k + c1 + c2 + c3
          + 2*SOTRec.w((p - 1), r)];
        elif flag[3] = p and flag[2] = q and (p + 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          return [n, 3 + c1 + c2 + c3];
        fi;
      ############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
      elif flag[1] = p^2*r then
        if flag[2] = p^2 and IsCyclic(Zen) then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
          return [n, 3 + c1 + c2 + c3 + c4];
        elif flag[3] = p^2 and flag[2] = r then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)];
        elif flag[3] = p^2 and flag[2] = 1 then ## q \mid (p - 1), q | (r - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
          gens:= [pcgsq[1], Filtered(pcgsp, x->Order(x) = p^2)[1], Filtered(pcgsp, x->Order(x) = p^2)[1]^p, pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogMod(ExponentsOfPcElement(G, gens[3]^gens[1])[3], Int(v^((p^2-p)/q)), p)) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          k := LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(r)), a^((r - 1)/q)) mod q;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)];
        elif flag[2] = p*r then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times (C_p \times C_r)
          return [n, 3 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)];
        elif (p - 1) mod q = 0 and flag[3] = p and flag[2] = r and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
          gens:= [pcgsq[1], pcgsp[1], pcgsp[2], pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1q := ExponentsOfPcElement(G, gens[2]^gens[1]);
          expp2q := ExponentsOfPcElement(G, gens[3]^gens[1]);
          x := Inverse(LogFFE(Eigenvalues(GF(p), [expp1q{[2, 3]}, expp2q{[2, 3]}]* One(GF(p)))[1], b^((p-1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          matq := [expp1q{[2, 3]}, expp2q{[2, 3]}]^x * One(GF(p));
          det := LogFFE((LogFFE(DeterminantMat(matq), b^((p-1)/q)) - 1)*One(GF(q)), c) mod (q - 1);
          if det < (q + 1)/2 then
            k := det;
          else
            k := (q - 1) - det;
          fi;
          return [n, 3 + k + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)];
        elif flag[3] = p and flag[2] = r and q = 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)];
        elif (p + 1) mod q = 0 and flag[2] = r and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)];
        elif flag[2] = p^2 and IsElementaryAbelian(Zen) then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
          return [n, 3 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))];
        elif flag[2] = p and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
          gens := [pcgsq[1], pcgsr[1], Filtered(pcgsp, x-> not x in Zen)[1], Filtered(pcgsp, x-> x in Zen)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]*One(GF(r)), a^((r - 1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(p)), b^((p - 1)/q)) mod q;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))
          + SOTRec.w((r - 1), q)];
        elif flag[2] = p and q = 2 then
          return [n, 4 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))];
        elif flag[3] = p and flag[2] = 1 and q > 2 and (r - 1) mod q = 0 and (p - 1) mod q = 0 then ##(r - 1) mod q = 0 and (p - 1) mod q = 0, G \cong C_q \ltimes (C_r \times C_p^2)
          tmp := [];
          for k in [0..(q - 3)/2] do
            Add(tmp, AsSet([[0, k], [0, (- k) mod (q - 1)]]));
          od;
          for l in [1..(q - 3)/2] do
            for k in [0..(q - 1)/2] do
              Add(tmp, AsSet([[l, k], [(l - k) mod (q - 1), (- k) mod (q - 1)]]));
            od;
          od;
          Add(tmp, AsSet([[(q - 1)/2, (q - 1)/2], [0, (q - 1)/2]]));
          for l in [(q - 1)/2..q - 2] do
            for k in [0..(q - 3)/2] do
              Add(tmp, AsSet([[l, k], [(l - k) mod (q - 1), (- k) mod (q - 1)]]));
            od;
          od;
          gens := [pcgsq[1], pcgsr[1], pcgsp[1], pcgsp[2]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1q := ExponentsOfPcElement(G, gens[3]^gens[1]);
          expp2q := ExponentsOfPcElement(G, gens[4]^gens[1]);
          matq := [expp1q{[3, 4]}, expp2q{[3, 4]}]* One(GF(p));
          ev := List(Eigenvalues(GF(p), matq), x->LogFFE(LogFFE(x, b^((p - 1)/q))*One(GF(q)), c) mod (q - 1));
          if Length(ev) = 1 then
            x := LogFFE(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]*One(GF(r)), a^((r - 1)/q))*One(GF(q)), c) mod (q - 1);
            y := ev[1];
            z := ev[1];
          else
            x := LogFFE(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]*One(GF(r)), a^((r - 1)/q))*One(GF(q)), c) mod (q - 1);
            y := ev[1];
            z := ev[2];
          fi;
          if AsSet([[(x - y) mod (q - 1), (z - y) mod (q - 1)], [(x - z) mod (q - 1), (y - z) mod (q - 1)]]) in tmp then
            m := Position(tmp, AsSet([[(x - y) mod (q - 1), (z - y) mod (q - 1)], [(x - z) mod (q - 1), (y - z) mod (q - 1)]]));
          elif AsSet([[(x - y) mod (q - 1), (z - y) mod (q - 1)], [(y - x) mod (q - 1), (y - z) mod (q - 1)]]) in tmp then
            m := Position(tmp, AsSet([[(x - y) mod (q - 1), (z - y) mod (q - 1)], [(y - x) mod (q - 1), (y - z) mod (q - 1)]]));
          else
            m := Position(tmp, AsSet([[(x - z) mod (q - 1), (y - z) mod (q - 1)], [(z - x) mod (q - 1), (z - y) mod (q - 1)]]));
          fi;
          return [n, 3 + (m - 1) + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + 2*SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))
          + SOTRec.w((r - 1), q)];
        elif flag[3] = p and flag[2] = 1 and q = 2 then ## G \cong C_2 \ltimes (C_r \times C_p^2)
          return [n, 4 + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + 2*SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))];
        elif flag[3] = p and flag[2] = 1 and (p + 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          gens := [pcgsq[1], pcgsr[1], pcgsp[1], pcgsp[2]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]*One(GF(r)), a^((r - 1)/q))) mod q;
          expp1q := ExponentsOfPcElement(G, gens[3]^gens[1]);
          expp2q := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat_k := [expp1q{[3, 4]}, expp2q{[3, 4]}]^x * One(GF(p^2));
          ev := List(Eigenvalues(GF(p^2), mat_k), x -> LogFFE(x, PrimitiveElement(GF(p^2))^((p^2 - 1)/q)) mod q);
          tmp := [];
          for k in [1..(q - 1)] do
            Add(tmp, AsSet([k, k*p mod q]));
          od;
          if Position(tmp, AsSet(ev)) < (q + 1)/2 then
            m := Position(tmp, AsSet(ev));
          else
            m := (q - 1) - Position(tmp, AsSet(ev));
          fi;
          return [n, 3 + (m - 1) + c1 + c2 + c3 + c4
          + SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p - 1), q)
          + (q + 1)/2*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(q, 2))
          + 2*SOTRec.delta(q, 2)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))
          + (q - 1)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
          + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2))];
        fi;
      ############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
      elif flag[1] = p*r then
        if flag[3] = p and flag[2] = p then ## q | (r - 1), p | (r - 1), and G \cong (C_{p^2} \times C_q) \ltimes C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5];
        elif flag[3] = p^2 and flag[2] = p then ## q | (r - 1), p | (r - 1), and G \cong ((C_p \times C_q) \ltimes C_r) \times C_p
          return [n, 3 + c1 + c2 + c3 + c4 + c5
          + SOTRec.w((r - 1), p*q)];
        elif flag[2] = 1 then
          gens := [Filtered(pcgsp, x -> not x in FittingSubgroup(group))[1], pcgsq[1], Filtered(pcgsp, x-> x in FittingSubgroup(group))[1], pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          if IsOne(Comm(gens[2], gens[4])) then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
            return [n, 3 + c1 + c2 + c3 + c4 + c5
            + 2*SOTRec.w((r - 1), p*q)];
          else ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
            x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[4]^gens[2])[4]*One(GF(r)), a^((r - 1)/q))) mod q;
            pcgs := [gens[1], gens[2]^x, gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(p)), b^((p - 1)/q)) mod q;
            return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5
            + 2*SOTRec.w((r - 1), p*q)
            + SOTRec.w((p - 1), q)*SOTRec.w((r - 1), p)];
          fi;
        fi;
      ############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
      elif flag[1] = p*q*r then
        if flag[3] = p^2 and flag[2] = p*q then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6];
        elif flag[3] = p^2 and flag[2] = p*r then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + SOTRec.w((r - 1), p)];
        elif flag[3] = p^2 and flag[2] = p then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
          gens := [pcgsp[1], pcgsp[2], pcgsq[1], pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[3]^gens[1])[3]*One(GF(q)), c^((q - 1)/p))) mod p;
          k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(r)), a^((r - 1)/p)) mod p;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5 + c6
          + SOTRec.w((r - 1), p)
          + SOTRec.w((q - 1), p)];
        elif flag[3] = p and flag[2] = p*q then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + SOTRec.w((r - 1), p)
          + SOTRec.w((q - 1), p)
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p)];
        elif flag[3] = p and flag[2] = p*r then ## P \cong C_p^2, p | (q - 1) and G \cong C_p \times (C_p \ltimes C_q) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + SOTRec.w((r - 1), p)
          + SOTRec.w((q - 1), p)
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p)
          + SOTRec.w((r - 1), p)];
        elif flag[3] = p and flag[2] = p then ## P \cong C_p^2 and G \cong C_{p^2} \ltimes (C_q \times C_r)
          b := Pcgs(Zen)[1];
          gens := [Filtered(pcgsp, x->not x in Zen)[1], b, pcgsq[1], pcgsr[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[3]^gens[1])[3]*One(GF(q)), c^((q - 1)/p))) mod p;
          k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(r)), a^((r - 1)/p)) mod p;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5 + c6
          + 2*SOTRec.w((r - 1), p)
          + 2*SOTRec.w((q - 1), p)
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p)];
        fi;
      fi;
    else
      return [60, 13];
    fi;
end;
##########################################
SOTRec.IdGroupPQRS := function(group, n, fac)
local p, q, r, s, P, Q, R, S, H, u, v, w, k, l, flag, lst, sizefit,
    G, pcgs, pc, fgens, i, a, b, c, d, x, y, Id,
    c1, c2, c3, c4, c5, c6, exprp, exprq, expsp, expsq, expsr, expqp,
    pcgsp, pcgsq, pcgsr, pcgss;

    p := fac[1][1];
    q := fac[2][1];
    r := fac[3][1];
    s := fac[4][1];

    ####
    Assert(1, p < q and q < r and r < s);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    Assert(1, IsPrimeInt(s));

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);
    S := SylowSubgroup(group, s);
    pcgsp := Pcgs(P);
    pcgsq := Pcgs(Q);
    pcgsr := Pcgs(R);
    pcgss := Pcgs(S);

    u := Z(q);
    v := Z(r);
    w := Z(s);

    c1 := SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)
        + SOTRec.w((s - 1), p) + SOTRec.w((r - 1), p) + SOTRec.w((q - 1), p);
    c2 := (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q) + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p) + SOTRec.w((r - 1), (p*q));
    c3 := (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
        + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
        + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
        + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
        + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), (p*r))
        + SOTRec.w((s - 1), (p*q*r));

    flag := [Size(Centre(group))];

    if flag[1] = n then
      return [n, 1];
    else
      pcgs := [pcgsp[1], pcgsq[1], pcgsr[1], pcgss[1]];
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      exprp := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
      exprq := ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]);
      expsp := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
      expsq := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
      expsr := ExponentsOfPcElement(pc, pcgs[4]^pcgs[3]);
      expqp := ExponentsOfPcElement(pc, pcgs[2]^pcgs[1]);
    fi;

    if flag[1] = p * q then
      return [n, 2];
    elif flag[1] = p * r then
      return [n, 2 + SOTRec.w((s - 1), r)];
    elif flag[1] = p * s then
      return [n, 2 + SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q)];
    elif flag[1] = q * r then
      return [n, 2 + SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)];
    elif flag[1] = q * s then
      return [n, 2 + SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q)
      + SOTRec.w((r - 1), q) + SOTRec.w((s - 1), p)];
    elif flag[1] = r * s then
      return [n, 2 + SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q)
      + SOTRec.w((s - 1), p) + SOTRec.w((r - 1), q) + SOTRec.w((r - 1), p)];
    elif flag[1] = p then
      if expsq[4] <> 1 and exprq[3] <> 1 and expsr[4] = 1 then
        x := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        k := LogFFE(expsq[4]^x*One(GF(s)), w^((s - 1)/q)) mod q;
        return [n, 2 + c1 + k - 1];
      elif expsq[4] <> 1 and expsr[4] <> 1 and exprq[3] = 1 then
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)];
      fi;
    elif flag[1] = q then
      if exprp[3] <> 1 and expsp[4] <> 1 and expsr[4] = 1 then
        x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r)) + k - 1];
      elif expsp[4] <> 1 and expsr[4] <> 1 and exprp[3] = 1 then
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)];
      fi;
    elif flag[1] = r then
      if expqp[2] <> 1 and expsp[4] <> 1 and expsq[4] = 1 then
        x := Inverse(LogFFE(expqp[2]*One(GF(q)), u^((q - 1)/p))) mod p;
        k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*r)) + k - 1];
      elif expsp[4] <> 1 and expsq[4] <> 1 and expqp[2] = 1 then
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)];
      fi;
    elif flag[1] = s then
      if exprp[3] <> 1 and expqp[2] <> 1 and exprq[3] = 1 then
        x := Inverse(LogFFE(expqp[2]*One(GF(q)), u^((q - 1)/p))) mod p;
        k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*q)) + k - 1];
      elif exprp[3] <> 1 and exprq[3] <> 1 and expqp[2] = 1 then
        return [n, 2 + c1 + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
        + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)];
      fi;
    elif flag[1] = 1 then
      Add(flag, Size(DerivedSubgroup(group)));
      if flag[2] = q * r * s then
        x := Inverse(LogFFE(expqp[2]*One(GF(q)), u^((q - 1)/p))) mod p;
        k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
        l := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
        return [n, 2 + c1 + c2
        + l + (k - 1)*(p - 1) - 1 ];
      elif flag[2] = r * s then
        if (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 and
          exprp[3] <> 1 and
          exprq[3] <> 1 and
          expsp[4] <> 1 and
          expsq[4] <> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
          l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
          return [n, 2 + c1 + c2
          + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + l + (k - 1)*(q - 1) - 1 ];
        elif exprp[3] <> 1 and exprq[3] = 1 then
          if expsp[4] <> 1 and expsq[4] <> 1 then
            x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
            k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
            return [n, 2 + c1 + c2
            + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + k - 1 ];
          elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and expsp[4] = 1 then
            return [n, 2 + c1 + c2
            + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q)) ];
          fi;
        elif exprq[3] <> 1 and exprp[3] = 1 then
          if expsp[4] <> 1 and expsq[4] <> 1 then
            y := Inverse(LogFFE(expsq[4]*One(GF(s)), w^((s - 1)/q))) mod q;
            l := LogFFE(exprq[3]^y*One(GF(r)), v^((r - 1)/q)) mod q;
            return [n, 2 + c1 + c2
            + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + l - 1 ];
          elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and expsq[4] = 1 then
            return [n, 2 + c1 + c2
            + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
            + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q) ];
          fi;
        elif (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 and expsq[4] = 1
          and exprp[3] <> 1 and exprq[3] <> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
          return [n, 2 + c1 + c2
          + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
          + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
          + k - 1];
        elif (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 and expsp[4] = 1
          and exprp[3] <> 1 and exprq[3] <> 1 then
          y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
          return [n, 2 + c1 + c2
          + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
          + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
          + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
          + l - 1];
        fi;
      elif flag[2] = q * s then
        if (s - 1) mod r = 0 and (q - 1) mod p = 0 and expsp[4] = 1 then
          return [n, 2 + c1 + c2
          + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
          + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
          + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
          + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
          + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
          + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p)];
        elif (s - 1) mod r = 0 and (q - 1) mod p = 0 and expsp[4] <> 1 and expsr[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
          return [n, 2 + c1 + c2
          + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
          + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
          + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
          + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
          + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
          + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p)
          + SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
          + k - 1];
        fi;
      elif flag[2] = s then
        return [n, 1 + c1 + c2 + c3];
      fi;
    fi;
end;
