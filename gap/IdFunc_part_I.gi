msg.NewOmega := function(pgroup)
  local pcp, gens, rels, newgens, G, i;
    pcp := Pcp(Image(IsomorphismPcpGroup(pgroup)));
    gens := GeneratorsOfPcp(pcp);
    rels := RelativeOrdersOfPcp(pcp);
    newgens := Filtered(gens, x-> Order(x) = p);
    G := Group(newgens);
  return G;
end;
######################################################
msg.NewAgemo := function(pgroup)
  local pcp, gens, rels, newgens, G, i;
    pcp := Pcp(Image(IsomorphismPcpGroup(pgroup)));
    gens := GeneratorsOfPcp(pcp);
    rels := RelativeOrdersOfPcp(pcp);
    newgens := [];
    for i in [1..Length(gens)] do
      Add(newgens, gens[i]^rels[i]);
    od;
    G := Group(newgens);
  return G;
end;
######################################################
InstallGlobalFunction( MyIdSmallGroup, function(group)
	local length, n, PF, fac, k, p, q, r;
    n := Size(group);
		PF := Factors(n);
		length := Length(PF);
		fac := Collected(Factors(n));
		if Length(fac) = 1 then
			p := PF[1];
			k := length;
			return msg.IdPGroup(group);
		fi;

		if length = 2 and Length(fac) = 2 then
			return msg.IdGroupPQ(group);
		fi;

		if length = 3 and Length(fac) = 2 then
			return msg.IdGroupP2Q(group);
		fi;

		if length = 3 and Length(fac) = 3 then
			return msg.IdGroupPQR(group);
		fi;

		if length = 4 and Length(fac) = 2 and PF[1] = PF[2] and PF[3] = PF[4] then
			return msg.IdGroupP2Q2(group);
		fi;

		if length = 4 and Length(fac) = 2 and PF[2] = PF[3] then
			return msg.IdGroupP3Q(group);
		fi;

		if length = 4 and Length(fac) = 3 then
			return msg.IdGroupP2QR(group);
		fi;

		if length = 4 and Length(fac) = 4 then
			return msg.IdGroupPQRS(group);
		fi;

		if length > 4 then
			Print(("Groups of order "), n, (" is not available in mysmallgrps: MyIdSmallGroup (#) determines groups of order # up to isomorphism, where # factorises into at most 4 primes."));
		fi;
end);
######################################################
msg.IdPGroup := function(group)
  local n, PF, length, fac, p, k, data, i, Id, pcpgroup, pcp, gens, rels, pcgs, pc, a, b, c, d, m, x;
    n := Size(group);
    PF := Factors(n);
    length := Length(PF);
    fac := Collected(Factors(n));
    if Length(fac) = 1 then
      p := PF[1];
      k := length;
    fi;
    if k = 1 then
      Id := [n, 1];
    fi;

    if k = 2 then
      if Exponent(group) = n then
        Id := [n, 1];
      else Id := [n, 2];
      fi;
    fi;

    if k = 3 then
      if IsAbelian(group) then
        if Exponent(group) = n then
          Id := [n, 1];
        elif Exponent(group) = p^2 then
          Id := [n, 2];
        else Id := [n, 3];
        fi;
      elif Exponent(group) = p and p > 2 then
        Id := [n, 4];
      elif Exponent(group) > p and p > 2 then
        Id := [n, 5];
      elif p = 2 and Size(Omega(group, 2)) = 8 then Id := [8, 4];
      elif p = 2 and Size(Omega(group, 2)) = 2 then Id := [8, 5];
      fi;
    fi;

    if k = 4 and p > 2 then
      if IsAbelian(group) then
        if Exponent(group) = n then Id := [n, 1];
        elif Exponent(group) = p^3 then Id := [n, 2];
        elif Exponent(group) = p^2 and Size(FrattiniSubgroup(group)) = p^2 then Id := [n, 3];
        elif Exponent(group) = p^2 and Size(FrattiniSubgroup(group)) = p then Id := [n, 4];
        else Id := [n, 5];
        fi;
      elif Exponent(group) = p^2 and Exponent(Centre(group)) = p^2 then Id := [n, 6];
      elif Exponent(group) = p^3 and Exponent(Centre(group)) = p^2 then Id := [n, 7];
      elif Size(Centre(group)) = p^2 and Exponent(Centre(group)) = p then
        if Exponent(group/DerivedSubgroup(group)) = p then
          if IsPowerfulPGroup(group) then Id := [n, 8];
          else Id := [n, 11];
          fi;
        elif Exponent(group/DerivedSubgroup(group)) = p^2 then
          if IsPowerfulPGroup(group) then Id := [n, 10];
          else Id := [n, 9];
          fi;
        fi;
      elif [Size(Centre(group)), Exponent(group), IsAbelian(msg.NewOmega(group))] = [p, p^2, true] then
        Id := [n, 15];
      elif p > 3 and [Size(Centre(group)), Exponent(group), IsAbelian(msg.NewOmega(group))] = [p, p^2, false] then
        pcpgroup := Image(IsomorphismPcpGroup(group));
        pcp := Pcp(pcpgroup);
        gens := GeneratorsOfPcp( pcp );
        rels := RelativeOrdersOfPcp( pcp );
        b := Filtered(gens, x -> Order(x) = p^2 and x^p in Centre(pcpgroup))[1];
        c := b^p;
        if Length(Filtered(gens, x -> Order(x) = p and ExponentsByPcp(pcp, Comm(x, b)) = [0, 0, 0, 0] and not x in Centre(pcpgroup))) > 0 then d := Filtered(gens, x -> Order(x) = p and ExponentsByPcp(pcp, Comm(x, b)) = [0, 0, 0, 0] and not x in Centre(pcpgroup))[1];
        else d := Filtered([gens[1]^p, gens[2]^p, gens[3]^p, gens[4]^p], x -> not x in Centre(pcpgroup) and ExponentsByPcp(pcp, Comm(x, b)) = [0, 0, 0, 0])[1];
        fi;
        if Length(Filtered(gens, x -> Order(x) = p and ExponentsByPcp(pcp, Comm(x, b)) <> [0, 0, 0, 0])) > 0 then a := Filtered(gens, x -> Order(x) = p and ExponentsByPcp(pcp, Comm(x, b)) <> [0, 0, 0, 0])[1];
        else a := Filtered([gens[1]^p, gens[2]^p, gens[3]^p, gens[4]^p], ExponentsByPcp(pcp, Comm(x, b)) <> [0, 0, 0, 0])[1];
        fi;
        pcgs := [a, b, c, d];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        x := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[3];
        if Legendre(x, p) = 1 then Id := [n, 12];
        else Id := [n, 13];
        fi;
      elif Exponent(group) = p then Id := [n, 14];
      elif p = 3 then
        if Size(Filtered(Elements(group), x -> Order(x) < 4)) = 27 then Id := [81, 12];
        elif Size(Filtered(Elements(group), x -> Order(x) < 4)) = 63 then Id := [81, 13];
        elif Size(Filtered(Elements(group), x -> Order(x) < 4)) = 45 then Id := [81, 14];
        fi;
      fi;
    fi;

    if k = 4 and p = 2 then
      if IsAbelian(group) then
        if Exponent(group) = n then Id := [n, 1];
        elif Exponent(group) = p^3 then Id := [n, 2];
        elif Exponent(group) = p^2 and Size(Agemo(group, p)) = p^2 then Id := [n, 3];
        elif Exponent(group) = p^2 and Size(Agemo(group, p)) = p then Id := [n, 4];
        else Id := [n, 5];
        fi;
      elif Exponent(Centre(group)) = 4 and Exponent(Agemo(group, 2)) = 2 then Id := [n, 6];
      elif Exponent(Centre(group)) = 4 and Exponent(Agemo(group, 2)) = 4 then Id := [n, 11];
      elif Exponent(Centre(group)) = 2 and Size(Centre(group)) = 4 then
        if Size(Omega(group, 2)) = 16 then Id := [n, 7];
        elif Size(Omega(group, 2)) = 8 then Id := [n, 8];
        elif Size(Omega(group, 2)) = 4 then
          if Size(NormalSubgroups(group)) = 19 then Id := [n, 9];
          else Id := [n, 10];
          fi;
        fi;
      elif Size(Centre(group)) = 2 then
        if Size(Omega(group, 2)) = 8 then Id := [n, 12];
        elif Size(Omega(group, 2)) = 16 then Id := [n, 13];
        else Id := [n, 14];
        fi;
      fi;
    fi;
  return Id;
end;
######################################################
msg.IdGroupPQ := function(group)
  local n, p, q, Id;
    n := Size(group);
    p := Factors(n)[2];
    q := Factors(n)[1];
    if (q - 1) mod p <> 0 then Id := [n, 1];
    elif IsAbelian(group) then Id := [n, 1];
    else Id := [n, 2];
    fi;
  return Id;
end;
######################################################
msg.IdGroupP2Q := function(group)
  local n, fac, p, q, Id, a, b, c, d, P, Q, G, pcp, gens, rels, pcgs, pc, m, x, t, i, k;
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
    if IsAbelian(group) then
      if IsCyclic(P) then Id := [n, 1];
      else Id := [n, 2];
      fi;
    elif p > q and q > 2 and (p + 1) mod q = 0 then
      if IsElementaryAbelian(P) then Id := [n, 3];
      fi;
    elif (p - 1) mod q = 0 and q > 2 then
      if IsElementaryAbelian(P) then
        if Size(Centre(group)) = p then Id := [n, 3];
        elif Size(Centre(group)) = 1 then
          gens := [];
          Append(gens, Pcgs(Q));
          Append(gens, Pcgs(P));
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(Eigenvalues(GF(p), [ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3]],
          [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3]] ] * One(GF(p)))[1],
          a^((p - 1)/q))) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          m := [ [ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2], ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[3]], [ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[2], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]] ] * One(GF(p));
          if (LogFFE((LogFFE(DeterminantMat(m), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1)) < (q + 1)/2 then
            k := LogFFE((LogFFE(DeterminantMat(m), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
          else k := (q - 1) - LogFFE((LogFFE(DeterminantMat(m), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
          fi;
          Id := [n, 4 + k];
        fi;
      elif IsCyclic(P) then
        Id := [n, 5 + (q - 1)/2];
      fi;
    elif p > q and q = 2 then
      if IsElementaryAbelian(P) then
        if Size(Centre(group)) = p then Id := [n, 3];
        else Id := [n, 4];
        fi;
      else Id := [n, 5];
      fi;
    elif p = 2 and q = 3 then
      if IsCyclic(P) then Id := [12, 5];
      elif Size(Centre(group)) = 2 then Id := [12, 4];
      else Id := [12, 3];
      fi;
    elif (q - 1) mod p = 0 and q > 3 then
      if [ IsCyclic(P), Size(FittingSubgroup(group)) ] = [ false, p*q ] then Id := [n, 3];
      elif [ IsCyclic(P), Size(FittingSubgroup(group)) ] = [ true, p*q ] then Id := [n, 4];
      elif [ IsCyclic(P), Size(FittingSubgroup(group)) ] = [ true, q ] then Id := [n, 5];
      fi;
    fi;

  return Id;
end;
######################################################
msg.IdGroupPQR := function(group)
  local n, fac, p, q, r, a, b, k, G, Q, R, P, pcgs, newpcgs, pcp, gens, rels, pc, newpc, i, x, Id;
    n := Size(group);
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    a := Z(p);
    b := Z(q);

    if IsAbelian(group) then Id := [n, 1];
    elif Size(Centre(group)) = p then Id := [n, 2]; ##r | (q - 1)
    elif Size(Centre(group)) = q then Id := [n, 2 + msg.deltaDivisibility((q - 1), r)]; ##r |(p - 1)
    elif (q - 1) mod r = 0 and (p - 1) mod r = 0 and Size(FittingSubgroup(group)) = p * q then ##r |(p - 1) and r | (q - 1)
      gens := Pcgs(group);
      pcgs := [];
      rels := RelativeOrders(gens);
      for i in [1..3] do
        if rels[i] = r then pcgs[1] := gens[i]; fi;
        if rels[i] = q then pcgs[2] := gens[i]; fi;
        if rels[i] = p then pcgs[3] := gens[i]; fi;
      od;
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      x := Inverse(ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2]*One(GF(q)))*(b^((q-1)/r));
      newpcgs := [pcgs[1], pcgs[2]^(Int(x)), pcgs[3]];
      newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
      k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[3]^newpcgs[1])[3]*One(GF(p)), a^((p-1)/r)) mod r;
      Id := [n, 3 + k];

    elif (p - 1) mod q = 0 and Size(Centre(group)) = r then
      Id := [n, 2 + msg.deltaDivisibility((q - 1), r) + msg.deltaDivisibility((p - 1), r) + (r - 1)*msg.deltaDivisibility((q - 1), r) * msg.deltaDivisibility((p - 1), r)];
    elif (p - 1) mod r = 0 and (p - 1) mod q = 0 and Size(FittingSubgroup(group)) = p then
      Id := [n, 3 + msg.deltaDivisibility((q - 1), r) + msg.deltaDivisibility((p - 1), r) + (r - 1)*msg.deltaDivisibility((q - 1), r) * msg.deltaDivisibility((p - 1), r)];
    fi;
  return Id;
end;
######################################################
msg.IdGroupPQRS := function(group)
  local n, fac, p, q, r, s, u, v, w, k, l, G, pcgs, newpcgs, pcp, gens, rels, pc, newpc, i, a, b, c, d, x, y, Id;
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

    u := Z(q);
    v := Z(r);
    w := Z(s);

    if IsAbelian(group) then Id := [n, 1]; fi;
    if Size(Centre(group)) < n then
      gens := Pcgs(group);
      pcgs := [];
      rels := RelativeOrders(gens);
      for i in [1..4] do
        if rels[i] = p then pcgs[1] := gens[i]; fi;
        if rels[i] = q then pcgs[2] := gens[i]; fi;
        if rels[i] = r then pcgs[3] := gens[i]; fi;
        if rels[i] = s then pcgs[4] := gens[i]; fi;
      od;
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
    fi;
    if Order(FittingSubgroup(group)) = s and (s - 1) mod (p*q*r) = 0 then
      Id := [n, 2];
    fi;
    if Order(FittingSubgroup(group)) = r * s and (r - 1)*(s - 1) mod (p*q) = 0 then
      if Size(Centre(group)) = s then Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))];
      elif Size(Centre(group)) = r then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))];
      elif (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 and
      ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3] <> 1 and
      ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3] <> 1 and
      ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4] <> 1 and
      ExponentsOfPcElement(pc, pcgs[4]^pcgs[2])[4] <> 1 then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        newpcgs := [pcgs[1]^x, pcgs[2]^y, pcgs[3], pcgs[4]];
        newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
        k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[1])[4]*One(GF(s)), w^((s - 1)/p)) mod p;
        l := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[2])[4]*One(GF(s)), w^((s - 1)/q)) mod q;
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r)) + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + l + (k - 1)*(p - 1) - 1 ];
      elif (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 and ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]) = [0, 0, 1, 0] then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(s)), w^((s - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[2])[4]*One(GF(s)), w^((s - 1)/q))) mod q;
        if x > 0 and y > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2]^y, pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[3]^newpcgs[1])[3]*One(GF(r)), v^((r - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + k - 1 ];
        elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]) = [0, 0, 0, 1] then
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q)) ];
        fi;
      elif (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 and ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]) = [0, 0, 1, 0] then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(s)), w^((s - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[2])[4]*One(GF(s)), w^((s - 1)/q))) mod q;
        if x > 0 and y > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2]^y, pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          l := LogFFE(ExponentsOfPcElement(newpc, newpcgs[3]^newpcgs[2])[3]*One(GF(r)), v^((r - 1)/q)) mod q;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + l - 1 ];
        elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]) = [0, 0, 0, 1] then
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q) ];
        fi;
      elif (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]) = [0, 0, 0, 1] then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        if x > 0 and y > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2]^y, pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[1])[4]*One(GF(s)), w^((s - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + k - 1 ];
        elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]) = [0, 0, 0, 1] then
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q) ];
        fi;
      elif (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]) = [0, 0, 0, 1] then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(r)), v^((r - 1)/q))) mod p;
        if x > 0 and y > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2]^y, pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          l := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[2])[4]*One(GF(s)), w^((s - 1)/q)) mod q;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + l - 1 ];
        elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]) = [0, 0, 1, 0] then
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
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
        Id := [n, 1 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p) ];
      elif (s - 1) mod r = 0 and (q - 1) mod p = 0 and ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]) = [0, 0, 0, 1] then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))];
      elif (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(s)), w^((s - 1)/p))) mod p;
        y := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[3])[4]*One(GF(s)), w^((s - 1)/r))) mod r;
        if x > 0 and y > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2], pcgs[3]^y, pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[2]^newpcgs[1])[2]*One(GF(q)), u^((q - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + k - 1 ];
        fi;
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * s then
      Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
      + msg.deltaDivisibility((r - 1), (p*q))
      + msg.deltaDivisibility((s - 1), (p*q))
      + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
      + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
      + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
      + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
      + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
      + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
      + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
      + msg.deltaDivisibility((s - 1), (p*r))
      + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
      + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))];
    fi;
    if Order(FittingSubgroup(group)) = q * r * s then
      if Order(Centre(group)) = r * s then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), (q*r))];
      elif Order(Centre(group)) = q * s then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), (q*r))
        + msg.deltaDivisibility((q - 1), p) ];
      elif Order(Centre(group)) = q * r then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), (q*r))
        + msg.deltaDivisibility((q - 1), p)
        + msg.deltaDivisibility((r - 1), p)];
      elif Order(Centre(group)) = s then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]*One(GF(r)), v^((r - 1)/p))) mod p;
        if x > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2], pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[2]^newpcgs[1])[2]*One(GF(q)), u^((q - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), (q*r))
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + k - 1 ];
        fi;
      elif Order(Centre(group)) = r then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(s)), w^((s - 1)/p))) mod p;
        if x > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2], pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[2]^newpcgs[1])[2]*One(GF(q)), u^((q - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), (q*r))
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + k - 1 ];
        fi;
      elif Order(Centre(group)) = q then
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(s)), w^((s - 1)/p))) mod p;
        if x > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2], pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[3]^newpcgs[1])[3]*One(GF(r)), v^((r - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), (q*r))
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
          + k - 1 ];
        fi;
      else x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2]*One(GF(q)), u^((q - 1)/p))) mod p;
        if x > 0 then
          newpcgs := [pcgs[1]^x, pcgs[2], pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[3]^newpcgs[1])[3]*One(GF(r)), v^((r - 1)/p)) mod p;
          l := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[1])[4]*One(GF(s)), w^((s - 1)/p)) mod p;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), (q*r))
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
          + l + (k - 1)*(p - 1) - 1 ];
        fi;
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * r * s then
      if Order(Centre(group)) = p * s then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), (q*r))
        + msg.deltaDivisibility((q - 1), p)
        + msg.deltaDivisibility((r - 1), p)
        + msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
        + (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p) ];
      elif Order(Centre(group)) = p * r then
        Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
        + msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
        + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
        + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
        + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
        + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
        + msg.deltaDivisibility((s - 1), (q*r))
        + msg.deltaDivisibility((q - 1), p)
        + msg.deltaDivisibility((r - 1), p)
        + msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
        + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
        + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
        + (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
        + msg.deltaDivisibility((r - 1), q) ];
      else
        x := Inverse(LogFFE(ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3]*One(GF(r)), v^((r - 1)/q))) mod q;
        if x > 0 then
          newpcgs := [pcgs[1], pcgs[2]^x, pcgs[3], pcgs[4]];
          newpc := PcgsByPcSequence(FamilyObj(newpcgs[1]), newpcgs);
          k := LogFFE(ExponentsOfPcElement(newpc, newpcgs[4]^newpcgs[2])[4]*One(GF(s)), w^((s - 1)/q)) mod q;
          Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
          + msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
          + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
          + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
          + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
          + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
          + msg.deltaDivisibility((s - 1), (q*r))
          + msg.deltaDivisibility((q - 1), p)
          + msg.deltaDivisibility((r - 1), p)
          + msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
          + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
          + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
          + (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
          + msg.deltaDivisibility((r - 1), q)
          + msg.deltaDivisibility((s - 1), q)
          + k - 1 ];
        fi;
      fi;
    fi;
    if Order(FittingSubgroup(group)) = p * q * s then
      Id := [n, 2 + msg.deltaDivisibility((s - 1), (p*q*r))
      + msg.deltaDivisibility((r - 1), (p*q))
      + msg.deltaDivisibility((s - 1), (p*q))
      + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
      + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
      + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
      + (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
      + (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
      + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
      + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
      + msg.deltaDivisibility((s - 1), (p*r))
      + msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
      + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r))
      + msg.deltaDivisibility((s - 1), (q*r))
      + msg.deltaDivisibility((q - 1), p)
      + msg.deltaDivisibility((r - 1), p)
      + msg.deltaDivisibility((s - 1), p)
      + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
      + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
      + (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
      + (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
      + msg.deltaDivisibility((r - 1), q)
      + msg.deltaDivisibility((s - 1), q)
      + (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), q) ];
    fi;
  return Id;
end;
######################################################
msg.IdGroupP2Q2 := function(group)
  local n, fac, p, q, P, Q, a, b, c, d, e, f, func, gens, G, pcgs, pc, Id, k, l, x, y, mat, det, mat1, mat2;
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
      if IsCyclic(P) and IsCyclic(Q) then Id := [n, 1];
      elif IsCyclic(Q) then Id := [n, 2];
      elif IsCyclic(P) then Id := [n, 3];
      else Id := [n, 4];
      fi;
    fi;
    if Size(Centre(group)) < n then
      gens := [];
      Append(gens, Filtered(Pcgs(Q), x-> not x in Centre(group)));
      Append(gens, Filtered(Pcgs(Q), x-> not x in gens));
      Append(gens, Pcgs(P));
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
    fi;

    if ((p - 1) mod q = 0 and q > 2) or n = 36 then
      if IsCyclic(P) and IsCyclic(Q) and Size(Centre(group)) = q then
        Id := [n, 5];
      elif IsCyclic(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q then
        Id := [n, 6];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = q * p then
        Id := [n, 7];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = q then
        x := Inverse(LogFFE(
        Eigenvalues(GF(p), [[ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]]]*One(GF(p)))[1],
        a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        mat := [ [ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[4]],
         [ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]] ]*One(GF(p));
        if LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1) < (q + 1)/2 then
          k := LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod q;
        else k := (q - 1) - LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        fi;
        Id := [n, 6 + 2 + k ];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q * p and q > 2 then
        Id := [n, 6 + (q + 5)/2];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q * p and q = 2 then
        Id := [n, 9];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q and q > 2 then
        x := Inverse(LogFFE(
        Eigenvalues(GF(p), [[ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]]]*One(GF(p)))[1],
        a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        mat := [ [ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[4]],
         [ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]] ]*One(GF(p));
        if LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1)< (q + 1)/2 then
          k := LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        else k := (q - 1) - LogFFE((LogFFE(DeterminantMat(mat), a^((p - 1)/q)) - 1)*One(GF(q)), b) mod (q - 1);
        fi;
        Id := [n, 6 + (q + 5)/2 + k + 1 ];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q and q = 2 then
        Id := [n, 10];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 1 and q > 2 then
        Id := [n, 10 + q ];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 1 and q = 2 then
        Id := [n, 11];
      fi;
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      if IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = q then
        Id := [n, 5];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = q then
        Id := [n, 6];
      fi;
    fi;
    if n = 36 then
      if IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 3 then
        Id := [n, 12];
      elif IsCyclic(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 3 then
        Id := [n, 13];
      fi;
    fi;
    if ( p + 1) mod (q^2) = 0 and q > 2 and Size(Centre(group)) = 1 then
      Id := [n, 7];
    elif n = 36 and IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
      Id := [n, 14];
    fi;
    if (p - 1) mod (q^2) = 0 and q > 2 then
      if IsCyclic(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
        Id := [n, 11 + q];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = p then
        Id := [n, 12 + q];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
        x := Inverse(LogFFE(
        Eigenvalues(GF(p), [[ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]]]*One(GF(p)))[1],
        a^((p - 1)/q))) mod q;
        pcgs := [gens[1]^x, gens[1]^(x*p), gens[3], gens[4]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        mat1 := [ [ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[4]],
         [ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]] ]*One(GF(p));
        mat2 := [ [ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[3], ExponentsOfPcElement(pc, pcgs[3]^pcgs[2])[4]],
         [ExponentsOfPcElement(pc, pcgs[4]^pcgs[2])[3], ExponentsOfPcElement(pc, pcgs[4]^pcgs[2])[4]] ]*One(GF(p));
        l := LogFFE(DeterminantMat(mat2), a^((p - 1)/q)) mod q;
        if l <> 1 then
          k := LogMod((LogFFE(DeterminantMat(mat1), a^((p - 1)/(q^2))) - 1), Int(f), q^2) mod (q^2 - q);
          if k > (q^2 - q)/2 then
            Id := [n, 12 + q + (q^2 - q - k) + 1];
          else
            Id := [n, 12 + q + k + 1];
          fi;
        elif l = 1 then
          k := (LogFFE(DeterminantMat(mat1), a^((p - 1)/(q^2))) - 1)/q mod q;
          Id := [n, 12 + q + (q^2 - q + 2)/2 + k];
        fi;
      fi;
    fi;

    if q = 2 and p > 3 then
      if IsCyclic(P) and IsCyclic(Q) and Size(Centre(group)) = 2 then
        Id := [n, 5];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 2 * p then
        Id := [n, 6];
      elif IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 2 then
        Id := [n, 7];
      elif IsCyclic(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 2 then
        Id := [n, 8];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 2 * p then
        Id := [n, 9];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 2 then
        Id := [n, 10];
      elif IsElementaryAbelian(P) and IsElementaryAbelian(Q) and Size(Centre(group)) = 1 then
        Id := [n, 11];
      elif p mod 4 = 1 and IsCyclic(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
        Id := [n, 12];
      elif p mod 4 = 1 and IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = p then
        Id := [n, 13];
      elif p mod 4 = 1 and IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
        mat1 := [ [ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
         [ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ]*One(GF(p));
        mat2 := [ [ExponentsOfPcElement(G, gens[3]^gens[2])[3], ExponentsOfPcElement(G, gens[3]^gens[2])[4]],
         [ExponentsOfPcElement(G, gens[4]^gens[2])[3], ExponentsOfPcElement(G, gens[4]^gens[2])[4]] ]*One(GF(p));
        x := DeterminantMat(mat1);
        y := DeterminantMat(mat2);
        if [Int(x), Int(y)] = [p - 1, 1] then
          Id := [n, 14];
        elif [Int(x), Int(y)] = [1, 1] then
          Id := [n, 15];
        elif [Int(x), Int(y)] = [Int(-a^((p - 1)/4)), p - 1] then
          Id := [n, 16];
        fi;
      elif p mod 4 = 3 and IsElementaryAbelian(P) and IsCyclic(Q) and Size(Centre(group)) = 1 then
        Id := [n, 12];
      fi;
    fi;
  return Id;
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
local n, fac, p, q, P, Q, O, a, b, r1, r2, r3, s1, s2, s3, c, d, e, f, x, y, k, l, lst,
Id, gens, pc, pcgs, G, matGL2, matGL3, func, func2, tmp, ev, evm;
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
############ abelian groups:
  if IsAbelian(group) then
    if IsCyclic(P) then Id := [n, 1];
    elif Exponent(P) = p^2 then Id := [n, 2];
    elif Exponent(P) = p then Id := [n, 3];
    fi;
  fi;
############ case 1: no normal Sylow subgroup -- necessarily n = 24
  if not IsNormal(group, P) and not IsNormal(group, Q) then Id := [24, 4]; fi;
############ interlude: n = 24
  if n = 24 and not IsAbelian(group) then
    if [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [true, true, 4, 8] then
      Id := [24, 5];
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [true, true, 4, 2] then
      Id := [24, 6];
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [false, true, 8, 2] then
      Id := [24, 7];
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2)), Size(Centre(group))] = [false, true, 4, 4, 4] then
      O := Omega(P, 2);
      if IsNormal(group, O) then Id := [24, 9];
      else Id := [24, 8];
      fi;
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2)), Size(Centre(group))] = [false, true, 4, 4, 2] then
      Id := [24, 10];
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [false, true, 2, 8] then
      Id := [24, 11];
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [false, true, 4, 8] then
      O := Omega(P, 2);
      if IsNormal(group, O) then Id := [24, 13];
      else Id := [24, 12];
      fi;
    elif [IsNormal(group, P), IsNormal(group, P), Exponent(P), Size(Omega(P, 2))] = [ true, false, 4, 2 ] then
      Id := [24, 14];
    fi;
  fi;

############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
  if p > 2 and IsNormal(group, P) and IsNormal(group, Q) and IsAbelian(group) = false then
    if Exponent(P) = p then Id := [n, 4];
    elif Exponent(P) = p^2 then Id := [n, 5];
    fi;
  elif p = 2 and q > 3 and IsNilpotent(group) and IsAbelian(group) = false then
    if Size(Omega(P, 2)) = 8 then Id := [n, 4];
    elif Size(Omega(P, 2)) = 2 then Id := [n, 5];
    fi;
  fi;

############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
  if n <> 24 and IsNormal(group, Q) and not IsNormal(group, P) then ##it follows that (q - 1) mod p = 0
    ## class 1: when P = C_{p^3}
    if IsCyclic(P) and (q - 1) mod p = 0 then
      if Size(Centre(group)) = p^2 then Id := [n, 6];
      elif (q - 1) mod (p^2) = 0 and Size(Centre(group)) = p then Id := [n, 7];
      elif (q - 1) mod (p^3) = 0 and Size(Centre(group)) = 1 then Id := [n, 8];
      fi;
    ## class 2: when P = C_{p^2} \times C_p, there are at most three isom types of semidirect products of P \ltimes Q
    elif IsAbelian(P) and Exponent(P) = p^2 then
      if Exponent(Centre(group)) = p^2 then
        Id := [n, 7 + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      elif Exponent(Centre(group)) = p and Size(Centre(group)) = p^2 then
        Id := [n, 8 + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      elif (q - 1) mod (p^2) = 0 and Size(Centre(group)) = p then
        Id := [n, 9 + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      fi;
    ## class 3: when P is elementary abelian, there is at most one isom type of P \ltimes Q
    elif IsElementaryAbelian(P) and (q - 1) mod p = 0 then Id := [n, 9 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    ## class 4: when P is extraspecial + type, there is at most one isom type of P \ltimes Q
    elif not IsAbelian(P) and Exponent(P) = p and p > 2 then Id := [n, 10 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif not IsAbelian(P) and Exponent(P) = 4 and Size(Omega(P, 2)) = 8 then
      gens := Pcgs(group);
      c := Filtered(Elements(P), x->Order(x) = 4)[1];
      d := Filtered(gens, x->Order(x) = q)[1];
      if d^c = d then
        Id := [n, 11 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      else Id := [n, 10 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      fi;
    ## class 5: when P is extraspecial - type, there is at most one isom type of P \ltimes Q
    elif not IsAbelian(P) and Exponent(P) = p^2 and p > 2 then
      gens := Pcgs(group);
      c := Filtered(gens, x->Order(x) = p and not x in Centre(P))[1];
      d := Filtered(gens, x->Order(x) = q)[1];
      k := LogFFE(ExponentsOfPcElement(gens, d^c)[4]*One(GF(q)), r1) mod p;
      if k > 0 then
        Id := [n, 10 + k + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      else
        Id := [n, 11 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3) + (p - 1)];
      fi;
    ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
    elif not IsAbelian(P) and Size(Omega(P, 2)) = 2 then Id := [n, 12 + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    fi;
  fi;
############ case 4: nonabelian and only the Sylow p-subgroup is normal
  if n <> 24 and IsNormal(group, P) and not IsNormal(group, Q) then
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
      Id := [n, 6 + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    ## class 2: when P = C_{p^2} \times C_p, there are at most (q + 1) isomorphism types of Q \ltimes P
    elif IsAbelian(P) and Exponent(P) = p^2 and Size(Centre(group)) = p^2 then ## (C_q \ltimes C_p) \times C_{p^2}
      Id := [n, 7 + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsAbelian(P) and Exponent(P) = p^2 and Size(Centre(group)) = p then ## (C_q \ltimes C_{p^2}) \times C_p
      Id := [n, 8 + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsAbelian(P) and Exponent(P) = p^2 and Size(Centre(group)) = 1 and q > 2 then ## C_q \ltimes (C_{p^2} \times C_p)
      gens:= [Pcgs(Q)[1], Filtered(Pcgs(P), x->Order(x) = p^2)[1], Filtered(Pcgs(P), x->Order(x) = p^2)[1]^p, Filtered(Pcgs(P), x->Order(x) = p and not x = Filtered(Pcgs(P), x->Order(x) = p^2)[1]^p)[1]];
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
      x := Inverse(LogMod(ExponentsOfPcElement(G, gens[2]^gens[1])[3]*p + ExponentsOfPcElement(G, gens[2]^gens[1])[2], Int(s2), p^2)) mod q;
      pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      k := LogFFE(ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]*One(GF(p)), s1) mod q;
      Id := [n, 8 + k + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsAbelian(P) and Exponent(P) = p^2 and Size(Centre(group)) = 1 and q = 2 then ## C_q \ltimes (C_{p^2} \times C_p)
      Id := [n, 9];
    ## class 3: when P is elementary abelian
    elif IsElementaryAbelian(P) and Size(Centre(group)) = p^2 then ## (C_q \ltimes C_p) \times C_p^2
      Id := [n, 9 + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsElementaryAbelian(P) and Size(Centre(group)) = p and (p - 1) mod q = 0 and q > 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
      gens:= [Pcgs(Q)[1], Filtered(Pcgs(P), x->Order(x) = p and not x in Centre(group))[1], Filtered(Pcgs(P), x->Order(x) = p and not x in Centre(group))[2], Filtered(Pcgs(group), x->Order(x) = p and x in Centre(group))[1]];
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
      x := Inverse(LogFFE(Eigenvalues(GF(p),
      [[ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3]],
      [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3]]]* One(GF(p)))[1], s1)) mod q;
      pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
      pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
      matGL2 := [ [ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2], ExponentsOfPcElement(G, pcgs[2]^pcgs[1])[3]],
      [ExponentsOfPcElement(pc, pcgs[3]^gens[1])[2], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3]] ] * One(GF(p));
      if LogFFE((LogFFE(DeterminantMat(matGL2), s1) - 1)*One(GF(q)), b) mod (q - 1) < (q + 1)/2 then
        k := LogFFE((LogFFE(DeterminantMat(matGL2), s1) - 1)*One(GF(q)), b) mod (q - 1);
      else k := (q - 1) - LogFFE((LogFFE(DeterminantMat(matGL2), s1) - 1)*One(GF(q)), b) mod (q - 1);
      fi;
      Id := [n, 10 + k + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsElementaryAbelian(P) and Size(Centre(group)) = p and q = 2 then ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
      Id := [n, 10 + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsElementaryAbelian(P) and Size(Centre(group)) = p and (p + 1) mod q = 0 and q > 2 then
      Id := [n, 6 + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    ## below: (C_q \ltimes C_p^3) when q | (p - 1)
    elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and q = 2 then
      Id := [n, 11 + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
    elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p - 1) mod 3 = 0 and q = 3 then
      gens := [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(P)[3]];
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
      ev := Eigenvalues(GF(p), [ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
      [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
      [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)));
      if Length(ev) = 1 then
        Id := [n, 10 + (q + 1)/2*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p + 1), q)
        + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      else
        evm := msg.EigenvaluesWithMultiplicitiesGL3P([ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)), p);
        x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
        matGL3 := ([ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ])^x * One(GF(p));
        if LogFFE((LogFFE(DeterminantMat(matGL3), s1) - 2)*One(GF(q)), b) mod (q - 1) < (q + 1)/2 then
          k := LogFFE((LogFFE(DeterminantMat(matGL3), s1) - 2)*One(GF(q)), b) mod (q - 1);
        else k := (q - 1) - LogFFE((LogFFE(DeterminantMat(matGL3), s1) - 2)*One(GF(q)), b) mod (q - 1);
        fi;
        Id := [n, 10 + k + (q + 1)/2*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p + 1), q)
        + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      fi;
    elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p - 1) mod q = 0 and q > 3 then
      gens := [Pcgs(Q)[1], Pcgs(P)[1], Pcgs(P)[2], Pcgs(P)[3]];
      G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
      ev := Eigenvalues(GF(p), [ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
      [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
      [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)));
      if Length(ev) = 1 then
        Id := [n, 10 + (q - 3)*msg.deltaDivisibility((p - 1), q)
        + (q + 1)/2*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p + 1), q)
        + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p)
        + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
      fi;
      if Length(ev) <> 1 then
        if Length(ev) = 2 then
          evm := msg.EigenvaluesWithMultiplicitiesGL3P([ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
          [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
          [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)), p);
          x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
        elif Length(ev) = 3 then
          x := Inverse(LogFFE(
          Eigenvalues(GF(p), [ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
          [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
          [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)))[1],
          s1)) mod q;
        fi;
        matGL3 := ([ [ExponentsOfPcElement(G, gens[2]^gens[1])[2], ExponentsOfPcElement(G, gens[2]^gens[1])[3], ExponentsOfPcElement(G, gens[2]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[3]^gens[1])[2], ExponentsOfPcElement(G, gens[3]^gens[1])[3], ExponentsOfPcElement(G, gens[3]^gens[1])[4]],
        [ExponentsOfPcElement(G, gens[4]^gens[1])[2], ExponentsOfPcElement(G, gens[4]^gens[1])[3], ExponentsOfPcElement(G, gens[4]^gens[1])[4]] ] * One(GF(p)))^x;
        l := Eigenvalues(GF(p), matGL3);

        if Length(l) = 3 then
          tmp := func(q);
          y := List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q)));
          if lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))) in tmp then
            k := Position(tmp, lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))));
            Id := [n, 6 + k + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
            + msg.deltaDivisibility((q-1), p^3) + 3*q*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))
            + msg.deltaDivisibility((p+1), q)*(1 - msg.deltafunction(q, 2)) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
          else k := Position(func2(q), lst(List(y, x -> (LogFFE(x, b) mod (q - 1)))));
            Id := [n, 9 + k + (q - 3)*msg.deltaDivisibility((p - 1), q) + (q + 1)/2*msg.deltaDivisibility((p - 1), q)
            + msg.deltaDivisibility((p + 1), q) + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p)
            + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
          fi;

        elif Length(l) = 2 and List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q))) = [b^((q - 1)/2)] then
          Id := [n, 9 + ((q + 1)/2 + q - 3)*msg.deltaDivisibility((p - 1), q)
          + (q + 1)/2*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p + 1), q)
          + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p)
          + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
        else
          k := Position(Filtered([1..(q - 2)], x-> not x = (q - 1)/2), LogFFE(LogFFE(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1)[1], s1)*One(GF(q)), b) mod (q - 1));
          Id := [n, 9 + k + (q + 1)/2*msg.deltaDivisibility((p - 1), q)
          + msg.deltaDivisibility((p + 1), q) + (q - 1) + (5 + p)*msg.deltaDivisibility((q - 1), p)
          + 2*msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((q - 1), p^3)];
        fi;
      fi;
    elif IsElementaryAbelian(P) and Size(Centre(group)) = 1 and (p^2 + p + 1 ) mod q = 0 and q > 3 then
      Id := [n, 5 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
        + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
        + msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
    ## class 4: when P is extraspecial of type +
    elif (not IsAbelian(P) and Exponent(P) = p and (p - 1) mod q = 0) then
      if Size(Centre(group)) = p then ## q | (p - 1), Z(G) = C_p
        if n mod 2 = 1 then
          Id := [n, 7 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
            + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
            + msg.deltaDivisibility((p+1), q)*(1 - msg.deltafunction(q, 2)) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
        else Id := [n, 5 + 7*msg.deltafunction(p, 2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
          + 8*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
        fi;
      elif Size(Centre(group)) = 1 then ## q | (p - 1), Z(G) = 1
        if Size(DerivedSubgroup(group)) = p^2 and q > 2 then
          Id := [n, 8 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
          + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
          + msg.deltaDivisibility((p+1), q)*(1 - msg.deltafunction(q, 2)) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
        elif Size(DerivedSubgroup(group)) = p^2 and q = 2 then
          Id := [n, 5 + 7*msg.deltafunction(p,2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
            + 9*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
        elif Size(DerivedSubgroup(group)) = p^3 and q > 2 then
          gens := [Pcgs(Q)[1], Filtered(Pcgs(P), x -> not x in Centre(P))[1], Filtered(Pcgs(P), x -> not x in Centre(P))[2], Filtered(Pcgs(P), x->x in Centre(P))[1]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(p)), s1)) mod q;
          pcgs := [gens[1]^x, gens[2], gens[3], gens[4]];
          pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
          matGL3 := [ [ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[2], ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[2]^pcgs[1])[4]],
          [ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[2], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[3]^pcgs[1])[4]],
          [ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[2], ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[3], ExponentsOfPcElement(pc, pcgs[4]^pcgs[1])[4]] ] * One(GF(p));
          y := List(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1), x -> LogFFE(x, s1) mod q)[1];
          if y > (q + 1)/2 then
            k := Position([2..(q + 1)/2], (q + 1) - y);
          else k := Position([2..(q + 1)/2], y);
          fi;
          Id := [n, 8 + k + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
          + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
          + msg.deltaDivisibility((p+1), q)*(1 - msg.deltafunction(q, 2)) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
        fi;
      fi;
    elif not IsAbelian(P) and Exponent(P) = p and (p + 1) mod q = 0 and q > 2 and p > 2 then
      Id := [n, 6 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
        + msg.deltaDivisibility((q-1), p^3) + (15+q^2+10*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
        + msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
    ## class 5: when P is extraspecial of type -,
    elif not IsAbelian(P) and Exponent(P) = p^2 and (p - 1) mod q = 0 then
      if n mod 2 = 1 then
        Id := [n, 5 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
        + msg.deltaDivisibility((q-1), p^3) + (36+q^2+13*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)*(1 - msg.deltafunction(q, 2))/6
        + 2*msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((p^2+p+1), q)*(1 - msg.deltafunction(q, 3))];
      else
        Id := [n, 5 + 7*msg.deltafunction(p,2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
          + 10*msg.deltafunction(q, 2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n, 56)];
      fi;
    fi;
  fi;
  return Id;
end;
