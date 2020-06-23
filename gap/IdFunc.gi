
######################################################
msg.IdPGroup := function(group)
  local n, PF, length, fac, p, k, i, Id, flag, a, b, c, d, F, N, gens, pcgs, G, m, x, y;
    n := Size(group);
    PF := Factors(n);
    length := Length(PF);
    fac := Collected(Factors(n));
    if Length(fac) = 1 then
      p := PF[1];
      k := length;
    fi;
    if k = 1 then
      return [n, 1];
    fi;

    if k = 2 then
      if Exponent(group) = n then
        return [n, 1];
      else return [n, 2];
      fi;
    fi;

    if k = 3 then
      if IsAbelian(group) then
        if Exponent(group) = n then
          return [n, 1];
        elif Exponent(group) = p^2 then
          return [n, 2];
        else return [n, 3];
        fi;
      elif Exponent(group) = p and p > 2 then
        return [n, 4];
      elif Exponent(group) > p and p > 2 then
        return [n, 5];
      elif p = 2 and Size(Omega(group, 2)) = 8 then return [8, 4];
      elif p = 2 and Size(Omega(group, 2)) = 2 then return [8, 5];
      fi;
    fi;

    if k = 4 and p > 2 then
      F := FrattiniSubgroup(group);
      if IsAbelian(group) then
        flag := [Exponent(group), Size(F)];
        if flag[1] = n then return [n, 1];
        elif flag[1] = p^3 then return [n, 2];
        elif flag = [p^2, p^2] then return [n, 3];
        elif flag = [p^2, p] then return [n, 4];
        else return [n, 5];
        fi;
      else
        flag := [Exponent(group), IsPowerfulPGroup(group), Size(Centre(group)), IsAbelian(DerivedSubgroup(group)), Exponent(group/DerivedSubgroup(group)), Exponent(Centre(group))];
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
          d := Filtered(Pcgs(F), x -> not x in Centre(group))[1];
          N := Centralizer(group, F);
          if Exponent(N) = p then return [n, 15];
          else gens := Pcgs(group);
            a := Filtered(gens, x-> not x in N)[1];
            b := Filtered(Pcgs(N), x->Order(x) = p^2 and x^p in Centre(group))[1];
            pcgs := [a, b, b^p, d];
            G := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            x := Inverse(ExponentsOfPcElement(G, pcgs[2]^pcgs[1])[4]) mod p;
            y := ExponentsOfPcElement(G, pcgs[4]^(pcgs[1]^x))[3];
            if Legendre(y, p) = 1 then return [n, 12];
            else return [n, 13];
            fi;
          fi;
        elif flag = [9, false, 3, true, 3, 3] then
          if IsAbelian(Omega(group, 3)) then return [81, 15];
          else m :=  Size(Filtered(Elements(group), x -> Order(x) < 4));
            if m = 27 then return [81, 12];
            elif m = 63 then return [81, 13];
            elif m = 45 then return [81, 14];
            fi;
          fi;
        fi;
      fi;
    elif k = 4 and p = 2 then
      if IsAbelian(group) then
        flag := [Exponent(group), Size(Agemo(group, 2))];
        if flag[1] = 16 then return [16, 1];
        elif flag[1] = 8 then return [n, 2];
        elif flag = [4, 4] then return [n, 3];
        elif flag = [4, 2] then return [n, 4];
        else return [n, 5];
        fi;
      else
        flag := [Exponent(Centre(group)), Size(Agemo(group, 2)), Size(Centre(group)), Size(Omega(group, 2))];
        if flag{[1, 2]} = [4, 2] then return [16, 6];
        elif flag{[1, 2]} = [4, 4] then return [16, 11];
        elif flag{[1, 3, 4]} = [2, 4, 16] then return [16, 7];
        elif flag{[1, 3, 4]} = [2, 4, 8] then return [16, 8];
        elif flag{[1, 3, 4]} = [2, 4, 4] then
          if Size(NormalSubgroups(group)) = 19 then return [16, 9];
          else return [16, 10];
          fi;
        elif flag{[3, 4]} = [2, 8] then return [16, 12];
        elif flag{[3, 4]} = [2, 16] then return [16, 13];
        else return [16, 14];
        fi;
      fi;
    fi;
end;

######################################################
msg.IdGroupPQ := function(group)
  local n, p, q, Id;
    n := Size(group);
    p := Factors(n)[2];
    q := Factors(n)[1];
    if IsAbelian(group) then return [n, 1];
    else return [n, 2];
    fi;
end;
######################################################
msg.IdGroupP2Q := function(group)
  local n, fac, p, q, Id, a, b, c, d, flag, P, Q, gens, G, exps1, exps2, pcgs, pc, m1, m2, m, det, x, k;
    n := Size(group);
    fac := Factors(n);
    if not Length(fac) = 3 or fac[1] = fac[3] then
        Error("Argument has to be of the form p^2*q, where p, q are primes");
    fi;
    p := fac[2];
    if fac[2] = fac[1] then
      q := fac[3];
    else
      q := fac[1];
    fi;
    if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) then
      Error("wrong input");
    fi;
    ####
    a := Z(p);
    b := Z(q);
    c := ZmodnZObj(Int(Z(p)),p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c; else d := c + 1;
    fi;
    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    flag := [IsElementaryAbelian(P), Size(Centre(group)), Size(FittingSubgroup(group))];
    if IsAbelian(group) then
      if flag[1] = false then return [n, 1];
      else return [n, 2];
      fi;
    elif p > q and q > 2 and (p + 1) mod q = 0 then
      if flag[1] = true then return [n, 3];
      fi;
    elif (p - 1) mod q = 0 and q > 2 then
      if flag{[1, 2]} = [true, p] then return [n, 3];
      elif flag{[1, 2]} = [true, 1] then
        gens := [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exps1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exps2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        x := Inverse(LogFFE(Eigenvalues(GF(p), [ exps1{[2, 3]}, exps2{[2, 3]} ] * One(GF(p)))[1],
          a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[2], gens[3]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        m1 := ExponentsOfPcElement(pc, pcgs[2]^pcgs[1]){[2, 3]};
        m2 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]){[2, 3]};
        m := [ m1, m2 ] * One(GF(p));
        det := DeterminantMat(m);
        if (LogFFE((LogFFE(det, a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1)) < (q + 1)/2 then
          k := LogFFE((LogFFE(det, a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        else k := (q - 1) - LogFFE((LogFFE(det, a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        fi;
        return [n, 4 + k];
      elif flag[1] = false then
        return [n, 5 + (q - 1)/2];
      fi;
    elif p > q and q = 2 then
      if flag{[1, 2]} = [true, p] then return [n, 3];
      elif flag{[1, 2]} = [true, 1] then return [n, 4];
      elif flag[1] = false then return [n, 5];
      fi;
    elif p = 2 and q = 3 then
      if flag[1] = false then return [12, 5];
      elif flag[2] = 2 then return [12, 4];
      else return [12, 3];
      fi;
    elif (q - 1) mod p = 0 and q > 3 then
      if flag{[1, 3]} = [ true, p*q ] then return [n, 3];
      elif flag{[1, 3]} = [ false, p*q ] then return [n, 4];
      elif flag{[1, 3]} = [ false, q ] then return [n, 5];
      fi;
    fi;
end;
######################################################
msg.IdGroupPQR := function(group)
  local n, fac, p, q, r, a, b, k, G, Q, R, P, c1, c2, c3, c4, c5, pcgs, pcp, pc, x;
    n := Size(group);
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    a := Z(p);
    b := Z(q);

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);

    c1 := msg.deltaDivisibility((q - 1), r);
    c2 := msg.deltaDivisibility((p - 1), r);
    c3 := (r - 1)*msg.deltaDivisibility((q - 1), r) * msg.deltaDivisibility((p - 1), r);
    c4 := msg.deltaDivisibility((p - 1), q);
    c5 := msg.deltaDivisibility((p - 1), q*r);

    if IsAbelian(group) then return [n, 1];
    elif Size(Centre(group)) = p then return [n, 2]; ##r | (q - 1)
    elif Size(Centre(group)) = q then return [n, 2 + c1]; ##r |(p - 1)
    elif (q - 1) mod r = 0 and (p - 1) mod r = 0 and Size(FittingSubgroup(group)) = p * q then ##r |(p - 1) and r | (q - 1)
      pcgs := [Pcgs(R)[1], Pcgs(Q)[1], Pcgs(P)[1]];
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2]*One(GF(q)), b^((q-1)/r))) mod r;
      k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^(pcgs[1]^x))[3]*One(GF(p)), a^((p-1)/r)) mod r;
      return [n, 3 + k];

    elif (p - 1) mod q = 0 and Size(Centre(group)) = r then
      return [n, 2 + c1 + c2 + c3];
    elif (p - 1) mod r = 0 and (p - 1) mod q = 0 and Size(FittingSubgroup(group)) = p then
      return [n, 3 + c1 + c2 + c3];
    fi;
end;
######################################################
msg.IdGroupPQRS := function(group)
  local n, fac, p, q, r, s, P, Q, R, S, u, v, w, k, l, G, pcgs, newpcgs, pcp, gens, rels, pc, newpc, i, a, b, c, d, x, y, Id,
  c1, c2, c3, c4, c5, c6, exprp, exprq, expsp, expsq, expsr, expqp;
    n := Order(group);
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);
    S := SylowSubgroup(group, s);
    u := Z(q);
    v := Z(r);
    w := Z(s);

    if IsAbelian(group) then return [n, 1]; fi;
    if Size(Centre(group)) < n then
      pcgs := [Pcgs(P)[1], Pcgs(Q)[1], Pcgs(R)[1], Pcgs(S)[1]];
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      exprp := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
      exprq := ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]);
      expsp := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
      expsq := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
      expsr := ExponentsOfPcElement(pc, pcgs[4]^pcgs[3]);
      expqp := ExponentsOfPcElement(pc, pcgs[2]^pcgs[1]);
    fi;

    c1 := msg.deltaDivisibility((s - 1), (p*q*r));
    c2 := msg.deltaDivisibility((r - 1), (p*q))
    + msg.deltaDivisibility((s - 1), (p*q))
    + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
    + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
    + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
    + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
    + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
    + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
    + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p);
    c3 := msg.deltaDivisibility((s - 1), p*r)
    + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
    + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r));
    c4 := msg.deltaDivisibility((s - 1), (q*r));
    c5 := msg.deltaDivisibility((q - 1), p)
    + msg.deltaDivisibility((r - 1), p)
    + msg.deltaDivisibility((s - 1), p)
    + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
    + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
    + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
    + (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p);
    c6 := msg.deltaDivisibility((r - 1), q)
    + msg.deltaDivisibility((s - 1), q)
    + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), q);
    if Order(FittingSubgroup(group)) = s and (s - 1) mod (p*q*r) = 0 then
      return [n, 2];
    fi;
    if Order(FittingSubgroup(group)) = r * s and (r - 1)*(s - 1) mod (p*q) = 0 then
      if Size(Centre(group)) = s then return [n, 2 + c1];
      elif Size(Centre(group)) = r then
        return [n, 2 + c1
        + msg.deltaDivisibility((r - 1), (p*q))];
      elif (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 and
        exprp[3] <> 1 and
        exprq[3] <> 1 and
        expsp[4] <> 1 and
        expsq[4] <> 1 then
        x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
        l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
        return [n, 2 + c1
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + l + (k - 1)*(p - 1) - 1 ];
      elif (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 and exprq[3] = 1 then
        if expsp[4] <> 1 and expsq[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          y := Inverse(LogFFE(expsq[4]*One(GF(s)), w^((s - 1)/q))) mod q;
          k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + k - 1 ];
        elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and expsp[4] = 1 then
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q)) ];
        fi;
      elif (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 and exprp[3] = 1 then
        if expsp[4] <> 1 and expsq[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          y := Inverse(LogFFE(expsq[4]*One(GF(s)), w^((s - 1)/q))) mod q;
          l := LogFFE(exprq[3]^y*One(GF(r)), v^((r - 1)/q)) mod q;
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + l - 1 ];
        elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and expsq[4] = 1 then
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q) ];
        fi;
      elif expsq[4] = 1 then
        if exprp[3] <> 1 and exprq[3]<> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + k - 1 ];
        elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and expsq[4] = 1 then
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q) ];
          fi;
      elif expsp[4] = 1 then
        if exprp[3] <> 1 and exprq[3] <> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + l - 1 ];
        elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and exprq[3] = 1 then
          return [n, 2 + c1
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q)) ];
        fi;
      fi;
    fi;
    if Order(FittingSubgroup(group)) = q * s then
      if Order(Centre(group)) = q then
        return [n, 2 + c1 + c2];
      elif (s - 1) mod r = 0 and (q - 1) mod p = 0 and expsp[4] = 1 then
        return [n, 2 + c1 + c2
        + msg.deltaDivisibility((s - 1), p*r)];
      elif (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
        if expsp[4] <> 1 and expsr[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          y := Inverse(LogFFE(expsr[4]*One(GF(s)), w^((s - 1)/r))) mod r;
          k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
          return [n, 2 + c1 + c2
          + msg.deltaDivisibility((s - 1), p*r)
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + k - 1 ];
        fi;
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * s then
      return [n, 2 + c1 + c2 + c3];
    fi;
    if Order(FittingSubgroup(group)) = q * r * s then
      if Order(Centre(group)) = r * s then
        return [n, 2 + c1 + c2 + c3 + c4];
      elif Order(Centre(group)) = q * s then
        return [n, 2 +  c1 + c2 + c3 + c4
        + msg.deltaDivisibility((q - 1), p) ];
      elif Order(Centre(group)) = q * r then
        return [n, 2 + c1 + c2 + c3 + c4
        + msg.deltaDivisibility((q - 1), p)
        + msg.deltaDivisibility((r - 1), p)];
      elif Order(Centre(group)) = s then
        if exprp[3] <> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
          return [n, 2 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + k - 1 ];
        fi;
      elif Order(Centre(group)) = r then
        if expsp[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
          return [n, 2 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + k - 1 ];
        fi;
      elif Order(Centre(group)) = q then
        if expsp[4] <> 1 then
          x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
          k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
          return [n, 2 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
          + k - 1 ];
        fi;
      elif expqp[2] <> 1 then
        x := Inverse(LogFFE(expqp[2]*One(GF(q)), u^((q - 1)/p))) mod p;
        k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
        l := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
        return [n, 2 + c1 + c2 + c3 + c4
        + msg.deltaDivisibility((q - 1), p)
        + msg.deltaDivisibility((r - 1), p)
        + msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
        + l + (k - 1)*(p - 1) - 1 ];
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * r * s then
      if Order(Centre(group)) = p * s then
        return [n, 2 + c1 + c2 + c3 + c4 + c5];
      elif Order(Centre(group)) = p * r then
        return [n, 2 + c1 + c2 + c3 + c4 + c5
        + msg.deltaDivisibility((r - 1), q) ];
      elif exprq[3] <> 1 then
        x := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        k := LogFFE(expsq[4]^x*One(GF(s)), w^((s - 1)/q)) mod q;
        return [n, 2 + c1 + c2 + c3 + c4 + c5
        + msg.deltaDivisibility((r - 1), q)
        + msg.deltaDivisibility((s - 1), q)
        + k - 1 ];
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * q * s then
      return [n, 2 + c1 + c2 + c3 + c4 + c5 + c6];
    fi;
end;
######################################################
msg.IdGroupP2Q2 := function(group)
  local n, fac, p, q, P, Q, a, b, c, d, e, f, ind, gens, G, pcgs, pc, g, h, ev,
  gexp1, gexp2, gexp3, gexp4, pcexp1, pcexp2, pcexp3, pcexp4, Id, k, l, x, y, mat, det, mat1, mat2;
    n := Order(group);
    fac := Factors(n);
    if not List(Collected(fac), x->x[2]) = [2, 2] then
      Error("Argument has to be of the form p^2*q^2, where p, q are primes");
		fi;
    q := fac[1];
    p := fac[4];
    Q := SylowSubgroup(group, q);
    P := SylowSubgroup(group, p);
    a := Z(p);
    b := Z(q);
    c := ZmodnZObj(Int(Z(p)), p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c;
    else d := c + 1;
    fi;
    e := ZmodnZObj(Int(Z(q)), q^2);
    if not e^(q - 1) = ZmodnZObj(1, q^2) then
      f := e;
    else f := e + 1;
    fi;

    if IsAbelian(group) then
      if IsCyclic(P) and IsCyclic(Q) then return [n, 1];
      elif IsCyclic(Q) then return [n, 2];
      elif IsCyclic(P) then return [n, 3];
      else return [n, 4];
      fi;
    fi;
    if Size(Centre(group)) < n then
      gens := [];
      Append(gens, Filtered(Pcgs(Q), x-> not x in Centre(group)));
      Append(gens, Filtered(Pcgs(Q), x-> not x in gens));
      Append(gens, Pcgs(P));
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
      ind := [IsCyclic(P), IsCyclic(Q), Size(Centre(group))];
    fi;

    if ((p - 1) mod q = 0 and q > 2) or n = 36 then
      if ind = [true, true, q] then
        return [n, 5];
      elif ind = [true, false, q] then
        return [n, 6];
      elif ind = [false, true, q*p] then
        return [n, 7];
      elif ind = [false, true, q] then
        gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        x := Inverse(LogFFE(
        Eigenvalues(GF(p), [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p)))[1], a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[2]^x, gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        pcexp1 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
        pcexp2 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
        mat := [ pcexp1{[3, 4]}, pcexp2{[3, 4]} ]*One(GF(p));
        det := LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        if det < (q + 1)/2 then
          k := det;
        else k := (q - 1) - det;
        fi;
        return [n, 6 + 2 + k ];
      elif ind = [false, false, q * p] and q > 2 then
        return [n, 6 + (q + 5)/2];
      elif ind = [false, false, q * p] and q = 2 then
        return [n, 9];
      elif ind = [false, false, q] and q > 2 then
        gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        x := Inverse(LogFFE(
        Eigenvalues(GF(p), [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p)))[1], a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        pcexp1 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
        pcexp2 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
        mat := [ pcexp1{[3, 4]}, pcexp2{[3, 4]} ]*One(GF(p));
        det := LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        if det < (q + 1)/2 then
          k := det;
        else k := (q - 1) - det;
        fi;
        return [n, 6 + (q + 5)/2 + k + 1 ];
      elif ind = [false, false, q] and q = 2 then
        return [n, 10];
      elif ind = [false, false, 1] and q > 2 then
        return [n, 10 + q ];
      elif ind = [false, false, 1] and q = 2 then
        return [n, 11];
      fi;
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      if ind = [false, false, q] then
        return [n, 5];
      elif ind = [false, true, q] then
        return [n, 6];
      fi;
    fi;
    if n = 36 then
      if ind = [false, false, 3] then
        return [n, 12];
      elif ind = [true, false, 3] then
        return [n, 13];
      fi;
    fi;
    if ( p + 1) mod (q^2) = 0 and q > 2 and ind[3] = 1 then
      return [n, 7];
    elif n = 36 and ind = [false, true, 1] then
      return [n, 14];
    fi;
    if (p - 1) mod (q^2) = 0 and q > 2 then
      if ind = [true, true, 1] then
        return [n, 11 + q];
      elif ind = [false, true, p] then
        return [n, 12 + q];
      elif ind = [false, true, 1] then
        g := Filtered(Pcgs(Q), x -> Order(x)=q^2)[1];
        h := Filtered(Pcgs(P), x -> x^g <> x)[1];
        if Size(Centre(Group([g^q, Pcgs(P)[1], Pcgs(P)[2]]))) = p then
          gens := [g, g^q, h, Pcgs(Centre(Group([g^q, Pcgs(P)[1], Pcgs(P)[2]])))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          gexp1 := ExponentsOfPcElement(G, gens[3]^gens[2]);
          gexp2 := ExponentsOfPcElement(G, gens[4]^gens[2]);
          x := Inverse(LogFFE(Filtered(
          Eigenvalues(GF(p), [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p))), x-> x<>Z(p)^0)[1], a^((p - 1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2]^x, gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          pcexp1 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
          pcexp2 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
          pcexp3 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]);
          pcexp4 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
          mat1 := [ pcexp1{[3, 4]}, pcexp2{[3, 4]} ]*One(GF(p));
          mat2 := [ pcexp3{[3, 4]}, pcexp4{[3, 4]} ]*One(GF(p));
          ev := List(Eigenvalues(GF(p), mat1), x -> LogFFE(x, a^((p - 1)/(q^2))) mod q);
          if Length(ev) = 1 then k := 1;
          else k := Filtered(ev, x -> x <> 1)[1];
          fi;
          return [n, 12 + q + (q^2 - q + 2)/2 + k];
        else
          gens := [g, g^q, h, Filtered(Pcgs(P), x -> x <>h)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          gexp1 := ExponentsOfPcElement(G, gens[3]^gens[2]);
          gexp2 := ExponentsOfPcElement(G, gens[4]^gens[2]);
          x := Inverse(LogFFE(Filtered(
          Eigenvalues(GF(p), [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p))), x-> x<>Z(p)^0)[1], a^((p - 1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2]^x, gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          pcexp1 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
          pcexp2 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
          pcexp3 := ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]);
          pcexp4 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
          mat1 := [ pcexp1{[3, 4]}, pcexp2{[3, 4]} ]*One(GF(p));
          mat2 := [ pcexp3{[3, 4]}, pcexp4{[3, 4]} ]*One(GF(p));
          ev := List(Eigenvalues(GF(p), mat2), x -> LogMod(LogFFE(x, a^((p - 1)/q)), Int(f), q^2) mod (q^2 - q));
          if Length(ev) = 1 then k := 0;
            return [n, 12 + q + k + 1];
          elif Length(ev) > 1 then
            k := Filtered(ev, x -> x <> 0)[1];
            if k > (q^2 - q)/2 then
              return [n, 12 + q + (q^2 - q - k) + 1];
            else
              return [n, 12 + q + k + 1];
            fi;
          fi;
        fi;
      fi;
    fi;

    if q = 2 and p > 3 then
      if ind = [true, true, 2] then
        return [n, 5];
      elif ind = [false, true, 2 * p] then
        return [n, 6];
      elif ind = [false, true, 2] then
        return [n, 7];
      elif ind = [true, false, 2] then
        return [n, 8];
      elif ind = [false, false, 2 * p] then
        return [n, 9];
      elif ind = [false, false, 2] then
        return [n, 10];
      elif ind = [false, false, 1] then
        return [n, 11];
      elif p mod 4 = 1 and ind = [true, true, 1] then
        return [n, 12];
      elif p mod 4 = 1 and ind = [false, true, p] then
        return [n, 13];
      elif p mod 4 = 1 and ind = [false, true, 1] then
        gexp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        gexp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        gexp3 := ExponentsOfPcElement(G, gens[3]^gens[2]);
        gexp4 := ExponentsOfPcElement(G, gens[4]^gens[2]);
        mat1 := [gexp1{[3, 4]}, gexp2{[3, 4]}]*One(GF(p));
        mat2 := [gexp3{[3, 4]}, gexp4{[3, 4]}]*One(GF(p));
        x := DeterminantMat(mat1);
        y := DeterminantMat(mat2);
        if AsSet([Int(x), Int(y)]) = AsSet([p - 1, 1]) then
          return [n, 14];
        elif AsSet([Int(x), Int(y)]) = AsSet([1, 1]) then
          return [n, 15];
        elif (not a^0 in Eigenvalues(GF(p), mat1) and a^0 in Eigenvalues(GF(p), mat2)) or (not a^0 in Eigenvalues(GF(p), mat2) and a^0 in Eigenvalues(GF(p), mat1)) then
          return [n, 16];
        fi;
      elif p mod 4 = 3 and ind = [false, true, 1] then
        return [n, 12];
      fi;
    fi;
end;
######################################################
msg.EigenvaluesWithMultiplicitiesGL3P := function(mat, p)
  local l, det, evm;
    l := Eigenvalues(GF(p), mat);
    if Length(l) <> 2 then return false; fi;
    det := DeterminantMat(mat);
    if det = l[1]^2*l[2] then
      evm := [[l[1], 2], [l[2], 1]];
    else evm := [[l[1], 1], [l[2], 2]];
    fi;
  return evm;
end;

######################################################
msg.IdGroupP3Q := function(group)
  local n, fac, p, q, P, Q, O, a, b, r1, r2, r3, s1, s2, s3, c, d, e, f, g, h, x, y, k, l, tst, lst,
  Id, gens, pc, pcgs, G, exp1, exp2, exp3, matGL2, matGL3, det, func, func2, tmp, ev, evm, N1, N2,
  c1, c2, c3, c4, c5, c6, c7, c8, c9, c10;
    n := Size(group);
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
      Error("Argument must be of the form of p^3q"); fi;
    p := fac[2];
    if fac[1] = fac[2] then
    q := fac[4]; elif fac[3] = fac[4] then
    q := fac[1]; fi;
    func := function(q)
      local i, j, k, ll;
        ll := [];
        for i in [1..Int((q - 3)/3)] do
          for j in [i + 1..Int((q - 1 - i)/2)] do
            if ((q - 1 - i - j) mod (q - 1) <> i) and ((q - 1 - i - j) mod (q - 1) <> j) and (-i) mod (q - 1) <> j then
              Add(ll, AsSet([AsSet([-i mod (q - 1), j]), AsSet([-j mod (q - 1), -(i + j) mod (q - 1)]), AsSet([(i + j) mod (q - 1), i])]));
              Add(ll, AsSet([AsSet([-i mod (q - 1), -(i + j) mod (q - 1)]), AsSet([(i + j) mod (q - 1), j]), AsSet([-j mod (q - 1), i])]));
            fi;
          od;
        od;
      return ll;
    end;

    func2 := function(q)
      local i, ll;
        ll := [[0, 0, 0]];
        for i in [1..(q - 1)/2] do
          Add(ll, AsSet([AsSet([-i mod (q - 1), i]), AsSet([-i mod (q - 1), (-2*i) mod (q - 1)]), AsSet([2*i mod (q - 1), i])]));
        od;
      return ll;
    end;

    lst := function(set)
      local st;
        st := AsSet([AsSet([set[1], set[2]]), AsSet([(-set[2]) mod (q - 1), (set[1] - set[2]) mod (q - 1)]), AsSet([(set[2] - set[1]) mod (q - 1), -set[1] mod (q - 1)])]);
      return st;
    end;
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
    Q := SylowSubgroup(group, q);

    tst := [IsNormal(group, P), IsNormal(group, Q), IsElementaryAbelian(P), Exponent(P), Size(Centre(group))];
    if p = 2 then Add(tst, Size(Omega(P, 2))); fi;
  ############ enumeration
    c1 := msg.deltafunction(n, 24) + msg.deltaDivisibility((q - 1), p) + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3);
    c2 := 2*msg.deltaDivisibility((q - 1), p) + msg.deltaDivisibility((q - 1), p^2);
    c3 := msg.deltaDivisibility((q - 1), p);
    c4 := msg.deltaDivisibility((q - 1), p) + msg.deltafunction(p, 2);
    c5 := p*msg.deltaDivisibility((q - 1), p)*(1 - msg.deltafunction(p, 2)) + msg.deltafunction(p, 2);
    c6 := msg.deltaDivisibility((p - 1), q);
    c7 := (q + 1)*msg.deltaDivisibility((p - 1), q);
    c8 := (1 - msg.deltafunction(q, 2))*(
    1/6*(q^2 + 4*q + 9 + 4*msg.deltaDivisibility((q - 1), 3))*msg.deltaDivisibility((p - 1), q)
    + msg.deltaDivisibility((p^2 + p + 1), q)*(1 - msg.deltafunction(q, 3))
    + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2)))
    + 3*msg.deltafunction(q, 2);
    c9 := (1/2*(q + 3)*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p + 1), q))*(1 - msg.deltafunction(q, 2))*(1 - msg.deltafunction(p, 2))
    + 2*msg.deltafunction(q, 2);
    c10 := msg.deltaDivisibility((p - 1), q);
  ############ abelian groups:
    if IsAbelian(group) then
      if IsCyclic(P) then return [n, 1];
      elif Exponent(P) = p^2 then return [n, 2];
      elif Exponent(P) = p then return [n, 3];
      fi;
    fi;
  ############ case 1: no normal Sylow subgroup -- necessarily n = 24
    if not IsNormal(group, P) and not IsNormal(group, Q) then return [24, 4]; fi;
  ############ interlude: n = 24
    if n = 24 and not IsAbelian(group) then
      if [tst[1], tst[2], tst[4], tst[6]] = [ true, true, 4, 8 ] then
        return [24, 5];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, true, 4, 2 ] then
        return [24, 6];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 8, 2 ] then
        return [24, 7];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 4 ] then
        O := Omega(P, 2);
        if IsNormal(group, O) then return [24, 9];
        else return [24, 8];
        fi;
      elif [tst[1], tst[2], tst[4], tst[6], tst[5]] = [ false, true, 2, 8, 4 ] then
        return [24, 10];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 8 ] then
        d := Pcgs(Q)[1];
        repeat c := Random(Elements(P)); until not c in Centre(P) and d*c = c*d;
        O := Group([c, d, Pcgs(Centre(group))[1]]);
        if IsCyclic(O) then return [24, 12];
        else return [24, 11];
        fi;
      elif [tst[1], tst[2], tst[4], tst[6]] = [ false, true, 4, 2 ] then
        return [24, 13];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, false, 2, 8 ] then
        return [24, 14];
      elif [tst[1], tst[2], tst[4], tst[6]] = [ true, false, 4, 2 ] then
        return [24, 15];
      fi;
    fi;

  ############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
    if p > 2 and [tst[1], tst[2]] = [true, true] and IsAbelian(group) = false then
      if tst[4] = p then return [n, 4];
      elif tst[4] = p^2 then return [n, 5];
      fi;
    elif p = 2 and q > 3 and IsNilpotent(group) and IsAbelian(group) = false then
      if tst[6] = 8 then return [n, 4];
      elif tst[6] = 2 then return [n, 5];
      fi;
    fi;

  ############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
    if n <> 24 and [tst[1], tst[2]] = [false, true] then ##it follows that (q - 1) mod p = 0
      ## class 1: when P = C_{p^3}
      if IsCyclic(P) and (q - 1) mod p = 0 then
        if tst[5] = p^2 then return [n, 6];
        elif (q - 1) mod (p^2) = 0 and tst[5] = p then return [n, 7];
        elif (q - 1) mod (p^3) = 0 and tst[5] = 1 then return [n, 8];
        fi;
      ## class 2: when P = C_{p^2} \times C_p, there are at most three isom types of semidirect products of P \ltimes Q
      elif IsAbelian(P) and tst[4] = p^2 then
        if Exponent(Centre(group)) = p^2 then
          return [n, 6 + c1];
        elif Exponent(Centre(group)) = p and tst[5] = p^2 then
          return [n, 7 + c1];
        elif (q - 1) mod (p^2) = 0 and tst[5] = p then
          return [n, 8 + c1];
        fi;
      ## class 3: when P is elementary abelian, there is at most one isom type of P \ltimes Q
      elif tst[3] = true and (q - 1) mod p = 0 then return [n, 6 + c1 + c2];
      ## class 4: when P is extraspecial + type, there is at most one isom type of P \ltimes Q
      elif not IsAbelian(P) and tst[4] = p and p > 2 then return [n, 6 + c1 + c2 + c3];
      elif not IsAbelian(P) and tst[4] = 4 and tst[6] = 8 then
        d := Pcgs(Q)[1];
        repeat c := Random(Elements(P)); until not c in Centre(P) and d*c = c*d;
        O := Group([c, d, Pcgs(Centre(group))[1]]);
        if IsCyclic(O) then return [n, 11 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
        else return [n, 10 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
        fi;
      ## class 5: when P is extraspecial - type, there is at most one isom type of P \ltimes Q
      elif not IsAbelian(P) and Exponent(P) = p^2 and p > 2 then
        repeat c := Random(Elements(P)); until Order(c) = p and not c in Centre(P) and not IsCyclic(Group([c, Pcgs(Centre(P))[1]]));
        d := Pcgs(Q)[1];
        repeat g := Random(Elements(P)); until Order(g) = p^2 and g^p in Centre(P);
        h := g^p;
        gens := [c, g, h, d];;
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
        x := Inverse(ExponentsOfPcElement(G, gens[2]^gens[1])[3]) mod p;
        k := LogFFE(ExponentsOfPcElement(G, gens[4]^(gens[1]^x))[4]*One(GF(q)), r1) mod p;
        if k > 0 then
          return [n, 10 + k + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
        else
          return [n, 11 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3) + (p - 1)];
        fi;
      ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
      elif not IsAbelian(P) and tst[6] = 2 then return [n, 12 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      fi;
    fi;
  ############ case 4: nonabelian and only the Sylow p-subgroup is normal
    if n <> 24 and [tst[1], tst[2]] = [true, false] then
      if (p - 1) mod q = 0 then
        s1 := a^((p - 1)/q);

        c := ZmodnZObj(Int(Z(p)), p^3);
        if not c^(p - 1) = ZmodnZObj(1, p^2) then
          d := c;
        else d := c + 1;
        fi;
        s3 := d^((p^3 - p^2)/q);

        e := ZmodnZObj(Int(Z(p)), p^2);
        if not e^(p - 1) = ZmodnZObj(1, p^2) then
          f := e;
        else f := e + 1;
        fi;

        s2 := f^((p^2-p)/q);
      fi;

      ## class 1: when P is cyclic, there is at most isom type of semidirect products of Q \ltimes P #it follows that (p - 1) mod q = 0
      if IsCyclic(P) then
        return [n, 6];
      ## class 2: when P = C_{p^2} \times C_p, there are at most (q + 1) isomorphism types of Q \ltimes P
    elif IsAbelian(P) and tst[4] = p^2 and tst[5] = p^2 then ## (C_q \ltimes C_p) \times C_{p^2}
        return [n, 7];
      elif IsAbelian(P) and tst[4] = p^2 and tst[5] = p then ## (C_q \ltimes C_{p^2}) \times C_p
        return [n, 8];
      elif IsAbelian(P) and tst[4] = p^2 and tst[5] = 1 and q > 2 then ## C_q \ltimes (C_{p^2} \times C_p)
        repeat g := Random(Elements(P)); until Order(g) = p and not g in FrattiniSubgroup(P);
        h := Filtered(Pcgs(P), x -> Order(x) = p^2)[1];
        gens:= [Pcgs(Q)[1], h, h^p, g];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        x := Inverse(LogMod(ExponentsOfPcElement(G, gens[3]^gens[1])[3], Int(s2), p)) mod q;
        k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(p)), s1) mod q;
        return [n, 8 + k];
      elif IsAbelian(P) and tst[4] = p^2 and tst[5] = 1 and q = 2 then ## C_q \ltimes (C_{p^2} \times C_p)
        return [n, 9];
      ## class 3: when P is elementary abelian
    elif tst[3] = true and tst[5] = p^2 then ## (C_q \ltimes C_p) \times C_p^2
        return [n, 9 + (q - 1)];
      elif tst[3] = true and tst[5] = p and (p - 1) mod q = 0 and q > 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
        gens:= [Pcgs(Q)[1], Filtered(Pcgs(P), x->not x in Centre(group))[1], Filtered(Pcgs(P), x->not x in Centre(group))[2], Filtered(Pcgs(P), x->x in Centre(group))[1]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        x := Inverse(LogFFE(Eigenvalues(GF(p), [exp1{[2, 3]}, exp2{[2, 3]}]* One(GF(p)))[1], s1)) mod q;
        pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}]^x * One(GF(p));
        det := LogFFE((LogFFE(DeterminantMat(matGL2), s1) - 1)*One(GF(q)), b) mod (q - 1);
        if det < (q + 1)/2 then
          k := det;
        else k := (q - 1) - det;
        fi;
        return [n, 10 + k + (q - 1)];
      elif tst[3] = true and tst[5] = p and q = 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
        return [n, 10 + (q - 1)];
      elif tst[3] = true and tst[5] = p and (p + 1) mod q = 0 and q > 2 then
        return [n, 6 + (5 + p)*msg.deltaDivisibility((q - 1), p)];
      ## below: (C_q \ltimes C_p^3) when q | (p - 1)
      elif tst[3] = true and tst[5] = 1 and q = 2 then
        return [n, 12];
      elif tst[3] = true and tst[5] = 1 and (p - 1) mod 3 = 0 and q = 3 then
        gens := [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(P)[3]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        ev := Eigenvalues(GF(p), [exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p)));
        if Length(ev) = 1 then
          return [n, 10 + (q + 1)/2 + (q - 1)];
        else
          evm := msg.EigenvaluesWithMultiplicitiesGL3P([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]} ] * One(GF(p)), p);
          x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
          matGL3 := ([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}])^x * One(GF(p));
          det := LogFFE((LogFFE(DeterminantMat(matGL3), s1) - 2)*One(GF(q)), b) mod (q - 1);
          if det < (q + 1)/2 then
            k := det;
          else k := (q - 1) - det;
          fi;
          return [n, 10 + k + (q + 1)/2 + (q - 1)];
        fi;
      elif tst[3] = true and tst[5] = 1 and (p - 1) mod q = 0 and q > 3 then
        gens := [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(P)[3]];
        G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
        exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
        exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
        exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
        ev := Eigenvalues(GF(p), [exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p)));
        if Length(ev) = 1 then
          return [n, 10 + (q - 3) + (q + 1)/2 + (q - 1)];
        fi;
        if Length(ev) <> 1 then
          if Length(ev) = 2 then
            evm := msg.EigenvaluesWithMultiplicitiesGL3P([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p)), p);
            x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
          elif Length(ev) = 3 then
            x := Inverse(LogFFE(
            Eigenvalues(GF(p), [exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p)))[1],
            s1)) mod q;
          fi;
          matGL3 := ([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}])^x * One(GF(p));
          l := Eigenvalues(GF(p), matGL3);
          if Length(l) = 3 then
            tmp := func(q);
            y := List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q)));
            if lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))) in tmp then
              k := Position(tmp, lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))));
              return [n, 6 + k + 3*q + msg.deltaDivisibility((p^2+p+1), q)];
            else k := Position(func2(q), lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))));
              return [n, 9 + k + (q - 3) + (q + 1)/2 + (q - 1)];
            fi;

          elif Length(l) = 2 and List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q))) = [b^((q - 1)/2)] then
            return [n, 9 + 2*q - 2];
          else
            k := Position(Filtered([1..(q - 2)], x-> not x = (q - 1)/2), LogFFE(LogFFE(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1)[1], s1)*One(GF(q)), b) mod (q - 1));
            return [n, 9 + k + (q + 1)/2 + (q - 1)];
          fi;
        fi;
      elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p^2 + p + 1) mod q = 0 and q > 3 then
        return [n, 5 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
          + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
          + msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
      ## class 4: when P is extraspecial of type +
      elif (not IsAbelian(P) and Exponent(P) = p and (p - 1) mod q = 0) then
        if Size(Centre(group)) = p then ## q | (p - 1), Z(G) = C_p
          if n mod 2 = 1 then
            return [n, 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8];
          else return [n, 5 + 7*msg.deltafunction(p, 2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
            + 8*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
          fi;
        elif Size(Centre(group)) = 1 then ## q | (p - 1), Z(G) = 1
          if Size(DerivedSubgroup(group)) = p^2 and q > 2 then
            return [n, 8 + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))/6 + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
          elif Size(DerivedSubgroup(group)) = p^2 and q = 2 then
            return [n, 5 + 7*msg.deltafunction(p,2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
              + 9*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
          elif Size(DerivedSubgroup(group)) = p^3 and q > 2 then
            gens := [Pcgs(Q)[1], Filtered(Pcgs(P), x -> not x in Centre(P))[1], Filtered(Pcgs(P), x -> not x in Centre(P))[2], Filtered(Pcgs(P), x->x in Centre(P))[1]];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            x := Inverse(LogFFE(exp3[4] * One(GF(p)), s1)) mod q;
            matGL3 := ([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}])^x * One(GF(p));
            y := List(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1), x -> LogFFE(x, s1) mod q)[1];
            if y > (q + 1)/2 then
              k := Position([2..(q + 1)/2], (q + 1) - y);
            else k := Position([2..(q + 1)/2], y);
            fi;
            return [n, 8 + k + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))/6 + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
          fi;
        fi;
      elif not IsAbelian(P) and Exponent(P) = p and (p + 1) mod q = 0 and q > 2 and p > 2 then
        return [n, 7];
      ## class 5: when P is extraspecial of type -,
      elif not IsAbelian(P) and Exponent(P) = p^2 and (p - 1) mod q = 0 then
        if n mod 2 = 1 then
          return [n, 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9];
        else
          return [n, 5 + 7*msg.deltafunction(p, 2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
            + 10*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
        fi;
      fi;
    fi;
end;

######################################################
msg.IdGroupP2QR := function(group)
  local n, fac, primefac, p, q, r, P, Q, R, a, b, c, u, v, G, gens, pc, pcgs, g, h,
  c1, c2, c3, c4, c5, c6, c7, k, l, m, tmp, exp, exp1, exp2, expp1q, expp2q, expp1r, expp2r,
  matq, detq, matr, detr, matqr, evqr, mat, mat_k, Id, x, y, z, ev, lst, N1, N2;
    n := Size(group);
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 3 then
      Error("Argument must be of the form of p^2qr");
    fi;
    primefac := function(n)
      local i, j, tmp;
        tmp := [];
        for i in Collected(fac) do
          if i[2] = 2 then j := i[1];
          elif i[2] = 1 then Add(tmp, i[1]);
          fi;
        od;
        Sort(tmp);
        Add(tmp, j);
      return tmp;
    end;
    p := primefac(n)[3]; q := primefac(n)[1]; r := primefac(n)[2];
    if r = 2 then
      Error("r must be a prime greater than q");
    fi;
    a := Z(r);;
    b := Z(p);;
    c := Z(q);;

    u := ZmodnZObj(Int(Z(p)), p^2);;
    if not u^(p-1) = ZmodnZObj(1, p^2) then v := u;
    else v := u + 1;
    fi;

    P := SylowSubgroup(group, p);
    Q := SylowSubgroup(group, q);
    R := SylowSubgroup(group, r);

    c1 := msg.deltaDivisibility((r - 1), p^2*q);;
    c2 := msg.deltaDivisibility((q - 1), p^2) + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
    + (p^2 - p)*msg.deltaDivisibility((r - 1), p^2)*msg.deltaDivisibility((q - 1), p^2)
    + msg.deltaDivisibility((r - 1), p^2) + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p^2)
    + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p);;
    c3 := 1/2*(q*r+q+r+7)*msg.deltaDivisibility((p - 1), q*r)
    + msg.deltaDivisibility((p^2 - 1), q*r)*(1 - msg.deltaDivisibility((p - 1), q*r))*(1 - msg.deltafunction(q, 2))
    + 2*msg.deltaDivisibility((p + 1), r)*msg.deltafunction(q, 2);;
    c4 := 1/2*(r + 5)*msg.deltaDivisibility((p - 1), r) + msg.deltaDivisibility((p + 1), r);;
    c5 := 8*msg.deltafunction(q, 2)
    + (1 - msg.deltafunction(q, 2))*(1/2*(q - 1)*(q + 4)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
    + 1/2*(q - 1)*msg.deltaDivisibility((p + 1), q)*msg.deltaDivisibility((r - 1), q)
    + 1/2*(q + 5)*msg.deltaDivisibility((p - 1), q)
    + 2*msg.deltaDivisibility((r - 1), q)
    + msg.deltaDivisibility((p + 1), q));;
    c6 := msg.deltaDivisibility((r - 1), p)*(msg.deltaDivisibility((p - 1), q)*(1 + (q - 1)*msg.deltaDivisibility((r - 1), q))
    + 2*msg.deltaDivisibility((r - 1), q));;
    c7 := 2*(msg.deltaDivisibility((q - 1), p) + msg.deltaDivisibility((r - 1), p) +
    (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)) + msg.deltafunction(n, 60);

    if IsSolvable(group) then
      ############ abelian groups:
      if IsAbelian(group) and IsCyclic(P) then return [n, 1];
      elif IsAbelian(group) and IsElementaryAbelian(P) then return [n, 2];
      fi;
      ############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
      if Size(FittingSubgroup(group)) = r then return [n, 3]; ##C_{p^2q} \ltimes C_r
      ############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or (p^2 | (q - 1) or (r - 1)) or (p | (q - 1) and p | (r - 1))
      elif Size(FittingSubgroup(group)) = q*r then
        if Size(Centre(group)) = r then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          return [n, 3 + c1];
        elif Size(Centre(group)) = q then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
          return [n, 3 + c1 + (p^2 - p)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p^2)
          + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((q - 1), (p^2))];
        elif Size(Centre(group)) = 1 and IsCyclic(P) then
          gens := [Pcgs(P)[1], Pcgs(P)[2], Pcgs(Q)[1], Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp := ExponentsOfPcElement(G, gens[3]^gens[1]);

          if IsAbelian(Group([gens[2], gens[4]])) and not IsAbelian(Group([gens[2], gens[3]])) then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/(p^2)))) mod (p^2);
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
            k := LogFFE(exp1[4]*One(GF(r)), a^((r-1)/p)) mod p;
            return [n, 2 + k + c1 + msg.deltaDivisibility((q - 1), (p^2))];
          elif (not IsAbelian(Group([gens[2], gens[4]]))) and (not IsAbelian(Group([gens[2], gens[3]]))) then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/(p^2)))) mod (p^2);
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
            k := Position(msg.groupofunitsP2(p), LogFFE(exp1[4]*One(GF(r)), a^((r-1)/(p^2))) mod (p^2));
            return [n, 2 + k + c1 + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
            + msg.deltaDivisibility((q - 1), (p^2))];
          elif (not IsAbelian(Group([gens[2], gens[4]]))) and IsAbelian(Group([gens[2], gens[3]])) then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
            x := Inverse(LogFFE(exp[3]*One(GF(q)), c^((q-1)/p))) mod p;
            pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            exp1 := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
            k := LogFFE(exp1[4]*One(GF(r)), a^((r-1)/p)) mod p;
            return [n, 2 + k + c1 + msg.deltaDivisibility((r - 1), p^2) + (p^2 - p)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p^2)
            + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
            + msg.deltaDivisibility((q - 1), (p^2))];
          fi;
        elif Size(Centre(group)) = 1 and Exponent(group) = p * q * r then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
          return [n, 3 + c1 + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p^2)
          + msg.deltaDivisibility((r - 1), p^2) + (p^2 - p)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p^2)
          + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((q - 1), (p^2))];
        fi;
      ############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    elif Size(FittingSubgroup(group)) = p^2 and IsCyclic(P) and Size(Centre(group)) = 1 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
        return [n, 3 + c1 + c2];
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p - 1) mod (q*r) = 0 then
        N1 := Group([Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2]]);
        N2 := Group([Pcgs(R)[1], Pcgs(P)[1], Pcgs(P)[2]]);
        if Size(Centre(N1)) = p and Size(Centre(N2)) = p then
           return [n, 3 + c1 + c2 + msg.deltaDivisibility((p - 1), q*r)];
        elif Pcgs(R)[1]^Pcgs(Q)[1] = Pcgs(R)[1] and Size(Centre(N2)) = p and Size(Centre(N1)) = 1 then ##R acts trivially on one of the generators of P
          gens := [Pcgs(Q)[1]*Pcgs(R)[1], Pcgs(Q)[1], Filtered(Pcgs(P), x-> x^Pcgs(Q)[1] <> x and x^Pcgs(R)[1] <> x)[1], Pcgs(Centre(N2))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat := [exp1{[3, 4]}, exp2{[3, 4]}]*One(GF(p));
          ev := Eigenvalues(GF(p), mat);
          if Length(ev) = 1 then k := 1;
          else x := Inverse(LogFFE(Filtered(ev, x->Order(x) = q*r)[1], b^((p - 1)/(q*r)))) mod (q*r);
          matq := mat^x;
          k := LogFFE(Filtered(Eigenvalues(GF(p), matq), x->Order(x) = q)[1], b^((p - 1)/(q*r))) mod q;
          fi;
          return [n, 3 + (k - 1) + c1 + c2
          + 3*msg.deltaDivisibility((p - 1), q*r)];
        elif Pcgs(R)[1]^Pcgs(Q)[1] = Pcgs(R)[1] and Size(Centre(N1)) = p and Size(Centre(N2)) = 1 then ##Q acts trivially on one of the generators of P
          gens := [Pcgs(Q)[1]*Pcgs(R)[1], Pcgs(R)[1], Filtered(Pcgs(P), x-> x^Pcgs(Q)[1] <> x and x^Pcgs(R)[1] <> x)[1], Pcgs(Centre(N1))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          exp1 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[4]^gens[1]);
          mat := [exp1{[3, 4]}, exp2{[3, 4]}]*One(GF(p));
          ev := Eigenvalues(GF(p), mat);
          if Length(ev) = 1 then k := 1;
          else x := Inverse(LogFFE(Filtered(ev, x->Order(x) = q*r)[1], b^((p - 1)/(q*r)))) mod (q*r);
          matr := mat^x;
          k := LogFFE(Filtered(Eigenvalues(GF(p), matr), x->Order(x) = r)[1], b^((p - 1)/(q*r))) mod r;
          fi;
          return [n, 3 + (k - 1) + c1 + c2
          + 3*msg.deltaDivisibility((p - 1), q*r)
          + (q - 1) * msg.deltaDivisibility((p - 1), q*r)];
        elif Pcgs(R)[1]^Pcgs(Q)[1] = Pcgs(R)[1] and Size(Centre(N1)) = 1 and Size(Centre(N2)) = 1 then ## Q and R act nontrivially on both the generators of P
          gens := [Pcgs(Q)[1], Pcgs(R)[1], Pcgs(P)[1], Pcgs(P)[2]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1q := ExponentsOfPcElement(G, gens[3]^gens[1]);
          expp2q := ExponentsOfPcElement(G, gens[4]^gens[1]);
          expp1r := ExponentsOfPcElement(G, gens[3]^gens[2]);
          expp2r := ExponentsOfPcElement(G, gens[4]^gens[2]);
          matq := [expp1q{[3, 4]}, expp2q{[3, 4]}] * One(GF(p));
          matr := [expp1r{[3, 4]}, expp2r{[3, 4]}] * One(GF(p));
          x := Inverse(LogFFE(Eigenvalues(GF(p), matq)[1], b^((p-1)/q))) mod q;
          y := Inverse(LogFFE(Eigenvalues(GF(p), matr)[1], b^((p-1)/r))) mod r;
          if (p-1) mod (q*r) = 0 and q > 2 then
            tmp := [];
            for k in [0..(q - 1)/2] do
              for l in [0..(r - 1)/2] do
                Add(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]]));
              od;
            od;
            for k in [1..(q-3)/2] do
              for l in [(r+1)/2..(r-1)] do
                Add(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]]));
              od;
            od;
          fi;
          if (p-1) mod (q*r) = 0 and q = 2 then
            tmp := [];
            for l in [0..(r-1)/2] do
              Add(tmp, AsSet([[0, l], [0, (-l) mod (r - 1)]]));
            od;
          fi;
          detq := DeterminantMat(matq^x);
          k := LogFFE((LogFFE(detq, b^((p - 1)/q)) - 1)*One(GF(q)), c) mod (q - 1);
          detr := DeterminantMat(matr^y);
          l := LogFFE((LogFFE(detr, b^((p - 1)/r)) - 1)*One(GF(r)), a) mod (r - 1);
          m := Position(tmp, AsSet([[k, l], [(-k) mod (q - 1), (-l) mod (r - 1)]]));
          return [n, 3 + (m - 1) + c1 + c2
          + 3*msg.deltaDivisibility((p - 1), q*r)
          + (r - 1 + q - 1) * msg.deltaDivisibility((p - 1), q*r)];
        elif q = 2 and Pcgs(R)[1]^Pcgs(Q)[1] <> Pcgs(R)[1] then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
          return [n, 3 + c1 + c2
          + 3*msg.deltaDivisibility((p - 1), q*r)
          + ((r + 1)/2 + r - 1 + q - 1) * msg.deltaDivisibility((p - 1), q*r)];
        fi;
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = p then  ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
        return [n, 3 + c1 + c2
        + 2*msg.deltaDivisibility((p - 1), q*r)];
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p + 1) mod (q*r) = 0 and q > 2 then ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
        return [n, 3 + c1 + c2];
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p + 1) mod (q*r) = 0 and q = 2 then
        if IsAbelian(Group([Pcgs(Q)[1], Pcgs(R)[1]])) then ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
          return [n, 3 + c1 + c2];
        else ## qr | (p + 1), q = 2, and G \cong (C_2 \ltimes C_r)\ltimes C_p^2
          return [n, 4 + c1 + c2];
        fi;
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        return [n, 3 + c1 + c2];
      elif Size(FittingSubgroup(group)) = p^2 and IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        return [n, 3 + c1 + c2];

      ############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
      elif Size(FittingSubgroup(group)) = p^2*q then
        if IsCyclic(P) and Size(Centre(group)) = q then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
          return [n, 3 + c1 + c2 + c3];
        elif Size(Centre(group)) = p*q then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
          return [n, 3 + c1 + c2 + c3
          + msg.deltaDivisibility((p - 1), r)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = q and (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          gens := [Pcgs(R)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(Q)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1r := ExponentsOfPcElement(G, gens[2]^gens[1]);
          expp2r := ExponentsOfPcElement(G, gens[3]^gens[1]);
          matr := [expp1r{[2, 3]}, expp2r{[2, 3]}]*One(GF(p));
          x := Inverse(LogFFE(Eigenvalues(GF(p), matr)[1], b^((p-1)/r))) mod r;
          detr := LogFFE((LogFFE(DeterminantMat(matr^x), b^((p-1)/r)) - 1)*One(GF(r)), a) mod (r - 1);
          if detr < (r + 1)/2 then
            k := detr;
          else k := (r - 1) - detr;
          fi;
          return [n, 3 + k + c1 + c2 + c3
          + 2*msg.deltaDivisibility((p - 1), r)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = q and (p + 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          return [n, 3 + c1 + c2 + c3];
        fi;
      ############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
      elif Size(FittingSubgroup(group)) = p^2*r then
        if Size(Centre(group)) = p^2 and IsCyclic(Centre(group)) then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
          return [n, 3 + c1 + c2 + c3 + c4];
        elif IsCyclic(P) and Size(Centre(group)) = r then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)];
        elif IsCyclic(P) and Size(Centre(group)) = 1 then ## q \mid (p - 1), q | (r - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
          gens:= [Pcgs(Q)[1], Filtered(Pcgs(P), x->Order(x) = p^2)[1], Filtered(Pcgs(P), x->Order(x) = p^2)[1]^p, Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogMod(ExponentsOfPcElement(G, gens[3]^gens[1])[3], Int(v^((p^2-p)/q)), p)) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          k := LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(r)), a^((r - 1)/q)) mod q;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)];
        elif Size(Centre(group)) = p*r then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times (C_p \times C_r)
          return [n, 3 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)];
        elif (p - 1) mod q = 0 and IsElementaryAbelian(P) and Size(Centre(group)) = r and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
          gens:= [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          expp1q := ExponentsOfPcElement(G, gens[2]^gens[1]);
          expp2q := ExponentsOfPcElement(G, gens[3]^gens[1]);
          x := Inverse(LogFFE(Eigenvalues(GF(p),
          [expp1q{[2, 3]}, expp2q{[2, 3]}]* One(GF(p)))[1], b^((p-1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          matq := [expp1q{[2, 3]}, expp2q{[2, 3]}]^x * One(GF(p));
          if LogFFE((LogFFE(Determinant(matq), b^((p-1)/q)) - 1)*One(GF(q)), c) mod (q - 1) < (q + 1)/2 then
            k := LogFFE((LogFFE(Determinant(matq), b^((p-1)/q)) - 1)*One(GF(q)), c) mod (q - 1);
          else k := (q - 1) - LogFFE((LogFFE(Determinant(matq), b^((p-1)/q)) - 1)*One(GF(q)), c) mod (q - 1);
          fi;
          return [n, 3 + k + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = r and q = 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)];
        elif (p + 1) mod q = 0 and Size(Centre(group)) = r and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)];
        elif Size(Centre(group)) = p^2 and IsElementaryAbelian(Centre(group)) then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
          return [n, 3 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))];
        elif Size(Centre(group)) = p and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
          gens := [Pcgs(Q)[1], Pcgs(R)[1], Filtered(Pcgs(P), x-> not x in Centre(group))[1], Filtered(Pcgs(P), x-> x in Centre(group))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]*One(GF(r)), a^((r - 1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(p)), b^((p - 1)/q)) mod q;
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))
          + msg.deltaDivisibility((r - 1), q)];
        elif Size(Centre(group)) = p and q = 2 then
          return [n, 4 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and q > 2 and (r - 1) mod q = 0 and (p - 1) mod q = 0 then ##(r - 1) mod q = 0 and (p - 1) mod q = 0, G \cong C_q \ltimes (C_r \times C_p^2)
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
          gens := [Pcgs(Q)[1], Pcgs(R)[1], Pcgs(P)[1], Pcgs(P)[2]];
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
          fi;
          return [n, 3 + (m - 1) + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + 2*msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))
          + msg.deltaDivisibility((r - 1), q)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and q = 2 then ## G \cong C_2 \ltimes (C_r \times C_p^2)
          return [n, 4 + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + 2*msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p + 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          gens := [Pcgs(Q)[1], Pcgs(R)[1], Pcgs(P)[1], Pcgs(P)[2]];
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
          else m := (q - 1) - Position(tmp, AsSet(ev));
          fi;
          return [n, 3 + (m - 1) + c1 + c2 + c3 + c4
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q)*(1 - msg.deltafunction(q, 2))
          + 2*msg.deltafunction(q, 2)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))
          + (q - 1)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((p + 1), q)*(1 - msg.deltafunction(q, 2))];
        fi;
      ############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
      elif Size(FittingSubgroup(group)) = p*r then
        if IsElementaryAbelian(P) and Size(Centre(group)) = p then ## q | (r - 1), p | (r - 1), and G \cong (C_{p^2} \times C_q) \ltimes C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5];
        elif IsCyclic(P) and Size(Centre(group)) = p then ## q | (r - 1), p | (r - 1), and G \cong ((C_p \times C_q) \ltimes C_r) \times C_p
          return [n, 3 + c1 + c2 + c3 + c4 + c5
          + msg.deltaDivisibility((r - 1), p*q)];
        elif Size(Centre(group)) = 1 then
          gens := [Filtered(Pcgs(P), x -> not x in FittingSubgroup(group))[1], Pcgs(Q)[1], Filtered(Pcgs(P), x-> x in FittingSubgroup(group))[1], Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          if IsAbelian(Group([gens[2], gens[4]])) then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
            return [n, 3 + c1 + c2 + c3 + c4 + c5
            + 2*msg.deltaDivisibility((r - 1), p*q)];
          else ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
            x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[4]^gens[2])[4]*One(GF(r)), a^((r - 1)/q))) mod q;
            pcgs := [gens[1], gens[2]^x, gens[3], gens[4]];
            pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
            k := LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(p)), b^((p - 1)/q)) mod q;
            return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5
            + 2*msg.deltaDivisibility((r - 1), p*q)
            + msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), p)];
          fi;
        fi;
      ############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
      elif Size(FittingSubgroup(group)) = p*q*r then
        if IsCyclic(P) and Size(Centre(group)) = p*q then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6];
        elif IsCyclic(P) and Size(Centre(group)) = p*r then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + msg.deltaDivisibility((r - 1), p)];
        elif IsCyclic(P) and Size(Centre(group)) = p then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
          gens := [Pcgs(P)[1], Pcgs(P)[2], Pcgs(Q)[1], Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[3]^gens[1])[3]*One(GF(q)), c^((q - 1)/p))) mod p;
          k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(r)), a^((r - 1)/p));
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5 + c6
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((q - 1), p)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = p*q then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = p*r then ## P \cong C_p^2, p | (q - 1) and G \cong C_p \times (C_p \ltimes C_q) \times C_r
          return [n, 3 + c1 + c2 + c3 + c4 + c5 + c6
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)];
        elif IsElementaryAbelian(P) and Size(Centre(group)) = p then ## P \cong C_p^2 and G \cong C_{p^2} \ltimes (C_q \times C_r)
          b := Pcgs(Centre(group))[1];
          gens := [Filtered(Pcgs(P), x->not x in Centre(group))[1], b, Pcgs(Q)[1], Pcgs(R)[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[3]^gens[1])[3]*One(GF(q)), c^((q - 1)/p))) mod p;
          k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4]^x*One(GF(r)), a^((r - 1)/p));
          return [n, 3 + (k - 1) + c1 + c2 + c3 + c4 + c5 + c6
          + 2*msg.deltaDivisibility((r - 1), p)
          + 2*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p)];
        fi;
      fi;
    else return [60, 13];
    fi;
  return Id;
end;
