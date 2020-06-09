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
