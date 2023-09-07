############################################################################
## For the SOTGroupsInformation function, we use the following to distinguish SOT Ids and the SmallGroups Ids
############################################################################
SOTRec.sot := function(n)
	local i, sglav;
		i := 0;
		repeat
		  i := i + 1;
		  sglav := SMALL_AVAILABLE_FUNCS[i](n);
		until sglav <> fail or i = 11;
		return sglav <> fail;
	end;

SOTRec.Print := function(sot, args...)
    local stop, x;
    if sot then
        Print("\n\>\>\>\>\>\>\>SOT ");
        stop := "\<\<\<\<\<\<\<";
    else
        Print("\n\>\>\>");
        stop := "\<\<\<";
    fi;
    for x in args do
        #Print("\>\<", x);
        if IsString(x) then
            x := ReplacedString(x, " ", "\>\< ");
        fi;
        Print(x);
    od;
    Print(stop);
end;

##############################################################################
SOTRec.infoP2Q2 := function(n, fac)
  local sot, p, q, c, m, prop, i;
    sot := SOTRec.sot(n);
    p := fac[2][1];
    q := fac[1][1];
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    prop := [ [[q^2, 1], [p^2, 1]], [[q^2, 2], [p^2, 1]],
      [[q^2, 1], [p^2, 2]], [[q^2, 2], [p^2, 2]] ];

    #### Enumeration
    c := [];
    c[1] := SOTRec.w((p - 1), q) + SOTRec.w((p - 1), q^2);
    c[2] := SOTRec.w((p - 1), q);
    c[3] := 1/2*(q + 3 - SOTRec.w(2, q))*SOTRec.w((p - 1), q) + 1/2*(q^2 + q + 2)*SOTRec.w((p - 1), q^2) + (1 - SOTRec.w(2, q))*SOTRec.w((p + 1), q) + SOTRec.w((p + 1), q^2) + SOTRec.delta(n, 36);
    c[4] := 1/2*(q + 5 - SOTRec.w(2, q))*SOTRec.w((p - 1), q) + (1 - SOTRec.w(2, q))*SOTRec.w((p + 1), q) + SOTRec.delta(n, 36);
    m := Sum(c);

    ### Info
    Print("The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.\n");
    Print("These groups are sorted by their Sylow subgroups.");
    Print("\>\>");
    SOTRec.Print(sot, "1 - 4 are abelian and all Sylow subgroups are normal.");
    if n = 36 then
      SOTRec.Print(sot, "5 is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[1][2], " with Sylow ", q, "-subgroup ", prop[1][1], ".");
      SOTRec.Print(sot, "6 is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[2][2], " with Sylow ", q, "-subgroup ", prop[2][1], ".");
      SOTRec.Print(sot, "7 is non-abelian, non-nilpotent and has a normal Sylow 2-subgroup [4, 2] with Sylow 3-subgroup [9, 1].");
      SOTRec.Print(sot, "8 - 10 are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[3][2], " with Sylow ", q, "-subgroup ", prop[3][1], ".");
      SOTRec.Print(sot, "11 - 14 are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[3][2], " with Sylow ", q, "-subgroup ", prop[3][1], ".");
    else
      for i in [1..4] do
        if c[i] = 1 then
          SOTRec.Print(sot, 4+Sum([1..i],x->c[x]), " is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[i][2], " with Sylow ", q, "-subgroup ", prop[i][1], ".");
        elif c[i] > 1 then
          SOTRec.Print(sot, 5+Sum([1..i-1],x->c[x])," - ", 4+Sum([1..i],x->c[x]),
          " are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[i][2], " with Sylow ", q, "-subgroup ", prop[i][1], ".");
        fi;
      od;
    fi;
    Print("\<\<");
  end;
##############################################################################
SOTRec.infoP3Q := function(n, fac)
  local sot, p, q, c, m, syl, i;
    sot := SOTRec.sot(n);
    p := fac[2][1];
    q := fac[1][1];
    ####
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    syl := [[p^3, 1], [p^3, 2], [p^3, 5], [p^3, 3], [p^3, 4],
            [p^3, 1], [p^3, 2], [p^3, 5], [p^3, 3], [p^3, 4]];
    ######## enumeration
    c := [];
    c[1] := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3);
    c[2] := 2*SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c[3] := SOTRec.w((q - 1), p);
    c[4] := SOTRec.w((q - 1), p) + SOTRec.delta(p, 2);
    c[5] := p*SOTRec.w((q - 1), p)*(1 - SOTRec.delta(p, 2)) + SOTRec.delta(p, 2);
    c[6] := SOTRec.w((p - 1), q);
    c[7] := (q + 1)*SOTRec.w((p - 1), q);
    c[8] := (1 - SOTRec.delta(q, 2))*(
      1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3))*SOTRec.w((p - 1), q)
      + SOTRec.w((p^2 + p + 1), q)*(1 - SOTRec.delta(q, 3))
      + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(q, 2)))
      + 3*SOTRec.delta(q, 2);
    c[9] := (1/2*(q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(q, 2))*(1 - SOTRec.delta(p, 2))
    + 2*SOTRec.delta(q, 2);
    c[10] := SOTRec.w((p - 1), q);
    c[11] := SOTRec.delta(n, 24);
    m := Sum(c);

    Print("The groups of order p^3q are solvable by Burnside's pq-Theorem.\n");
    Print("These groups are sorted by their Sylow subgroups.");
    Print("\>\>");
    SOTRec.Print(sot, "1 - 3 are abelian.");
    SOTRec.Print(sot, "4 - 5 are nonabelian nilpotent and have a normal Sylow ", p,"-subgroup and a normal Sylow ", q, "-subgroup.");
    for i in [1..5] do
      if c[i] = 1 then
        SOTRec.Print(sot, 5+Sum([1..i],x->c[x])," is non-nilpotent and has a normal Sylow ", p, "-subgroup ", syl[i], ".");
      elif c[i] > 1 then
        SOTRec.Print(sot, 6+Sum([1..i-1],x->c[x])," - ", 5+Sum([1..i],x->c[x]),
        " are non-nilpotent and have a normal Sylow ", p, "-subgroup ", syl[i], ".");
      fi;
    od;
    for i in [6..10] do
      if c[i] = 1 then
        SOTRec.Print(sot, 5+Sum([1..i],x->c[x])," is non-nilpotent and has a normal Sylow ", q, "-subgroup with Sylow ", p, "-subgroup ", syl[i], ".");
      elif c[i] > 1 then
        SOTRec.Print(sot, 6+Sum([1..i-1],x->c[x])," - ", 5+Sum([1..i],x->c[x])," are non-nilpotent and have a normal Sylow ", q, "-subgroup with Sylow ", p, "-subgroup ", syl[i], ".");
      fi;
    od;
    if c[11] = 1 then
      SOTRec.Print(sot, "15 is non-nilpotent, isomorphic to Sym(4), and has no normal Sylow subgroups.");
    fi;
    Print("\<\<");
  end;
##############################################################################
SOTRec.infoP2QR := function(n, fac)
  local sot, p, q, r, m, c, fit, i;
    sot := SOTRec.sot(n);
    c := [];
    p := fac[3][1];
    q := fac[1][1];
    r := fac[2][1];
    ####
    Assert(1, r > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    fit := [r, q*r, p^2, p^2*q, p^2*r, p*r, p*q*r];
    ############ enumeration of distinct cases
    c[1] := SOTRec.w((r - 1), p^2*q);;
    c[2] := SOTRec.w((q - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
      + (p^2 - p)*SOTRec.w((r - 1), p^2)*SOTRec.w((q - 1), p^2)
      + SOTRec.w((r - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p^2)
      + SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p);;
    c[3] := 1/2*(q*r+q+r+7)*SOTRec.w((p - 1), q*r)
      + SOTRec.w((p^2 - 1), q*r)*(1 - SOTRec.w((p - 1), q*r))*(1 - SOTRec.delta(q, 2))
      + 2*SOTRec.w((p + 1), r)*SOTRec.delta(q, 2);;
    c[4] := 1/2*(r + 5)*SOTRec.w((p - 1), r) + SOTRec.w((p + 1), r);;
    c[5] := 8*SOTRec.delta(q, 2)
      + (1 - SOTRec.delta(q, 2))*(1/2*(q - 1)*(q + 4)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
      + 1/2*(q - 1)*SOTRec.w((p + 1), q)*SOTRec.w((r - 1), q)
      + 1/2*(q + 5)*SOTRec.w((p - 1), q)
      + 2*SOTRec.w((r - 1), q)
      + SOTRec.w((p + 1), q));;
    c[6] := SOTRec.w((r - 1), p)*(SOTRec.w((p - 1), q)*(1 + (q - 1)*SOTRec.w((r - 1), q))
      + 2*SOTRec.w((r - 1), q));;
    c[7] := 2*(SOTRec.w((q - 1), p) + SOTRec.w((r - 1), p)
      + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p));;
    m := Sum(c);
    if m = 0 then
      Print("All groups of order ", n, " are abelian.\n");
    else
      Print("The groups of order p^2qr are either solvable or isomorphic to Alt(5).\n");
      Print("The solvable groups are sorted by their Fitting subgroup.");
      Print("\>\>");
      SOTRec.Print(sot, "1 - 2 are the nilpotent groups." );
      for i in [1..7] do
        if c[i] = 1 then
          SOTRec.Print(sot, 2+Sum([1..i],x->c[x])," has Fitting subgroup of order ", fit[i], ".");
        elif c[i] > 1 then
          SOTRec.Print(sot, 3+Sum([1..i-1],x->c[x])," - ", 2+Sum([1..i],x->c[x]), " have Fitting subgroup of order ", fit[i], ".");
        fi;
      od;
      if n = 60 then
        SOTRec.Print(sot, "13 is nonsolvable and has Fitting subgroup of order 1.");
      fi;
    fi;
    Print("\<\<");
  end;
##############################################################################
SOTRec.infoP4Q := function(n, fac)
    local sot, p, q, c, c0, m, prop, i, j;
    sot := SOTRec.sot(n);
    p := fac[2][1];
    q := fac[1][1];
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    prop := [];
    if p > 3 then
        prop[1] := [, "cylic", [p^4, 1]];
        prop[2] := [, "abelian", [p^4, 5]];
        prop[3] := [, "abelian", [p^4, 2]];
        prop[4] := [, "abelian", [p^4, 11]];
        prop[5] := [, "elementary abelian", [p^4, 15]];
        prop[6] := [, "nonabelian", [p^4, 14]];
        prop[7] := [, "nonabelian", [p^4, 6]];
        prop[8] := [, "nonabelian", [p^4, 13]];
        prop[9] := [, "nonabelian", [p^4, 3]];
        prop[10] := [, "nonabelian", [p^4, 4]];
        prop[11] := [, "nonabelian", [p^4, 12]];
        prop[12] := [, "nonabelian", [p^4, 9]];
        prop[13] := [, "nonabelian", [p^4, 10]];
        prop[14] := [, "nonabelian", [p^4, 7]];
        prop[15] := [, "nonabelian", [p^4, 8]];
    elif p = 3 then
        prop[1] := [, "cylic", [p^4, 1]];
        prop[2] := [, "abelian", [p^4, 5]];
        prop[3] := [, "abelian", [p^4, 2]];
        prop[4] := [, "abelian", [p^4, 11]];
        prop[5] := [, "elementary abelian", [p^4, 15]];
        prop[6] := [, "nonabelian", [p^4, 14]];
        prop[7] := [, "nonabelian", [p^4, 6]];
        prop[8] := [, "nonabelian", [p^4, 13]];
        prop[9] := [, "nonabelian", [p^4, 3]];
        prop[10] := [, "nonabelian", [p^4, 4]];
        prop[11] := [, "nonabelian", [p^4, 12]];
        prop[12] := [, "nonabelian", [p^4, 8]];
        prop[13] := [, "nonabelian", [p^4, 9]];
        prop[14] := [, "nonabelian", [p^4, 7]];
        prop[15] := [, "nonabelian", [p^4, 10]];
    elif p = 2 then
        prop[1] := [, "cylic", [p^4, 1]];
        prop[2] := [, "abelian", [p^4, 5]];
        prop[3] := [, "abelian", [p^4, 2]];
        prop[4] := [, "abelian", [p^4, 10]];
        prop[5] := [, "elementary abelian", [p^4, 14]];
        prop[6] := [, "nonabelian", [p^4, 13]];
        prop[7] := [, "nonabelian", [p^4, 11]];
        prop[8] := [, "nonabelian", [p^4, 3]];
        prop[9] := [, "nonabelian", [p^4, 12]];
        prop[10] := [, "nonabelian", [p^4, 4]];
        prop[11] := [, "nonabelian", [p^4, 6]];
        prop[12] := [, "nonabelian", [p^4, 8]];
        prop[13] := [, "nonabelian", [p^4, 7]];
        prop[14] := [, "nonabelian", [p^4, 9]];
    fi;

    #### Enumeration
    c0 := 15 - SOTRec.delta(2, p);
    c := [];
    c[1] := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3) + SOTRec.w((q - 1), p^4);
    c[2] := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3);
    c[3] := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c[4] := 2*SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c[5] := SOTRec.w((q - 1), p);
    c[6] := 3*SOTRec.w((q - 1), p);
    c[7] := (1 - SOTRec.delta(2, p))*(p*SOTRec.w((q - 1), p) + p*SOTRec.w((q - 1), p^2)) + 3*SOTRec.delta(2, p);
    c[8] := (1 - SOTRec.delta(2, p))*(p + 1)*SOTRec.w((q - 1), p) + SOTRec.delta(2, p)*(2 + SOTRec.w((q - 1), 4));
    c[9] := 2*SOTRec.w((q - 1), p) + (1 - SOTRec.delta(2, p))*SOTRec.w((q - 1), p^2);
    c[10] := p*SOTRec.w((q - 1), p) + (p - 1)*SOTRec.w((q - 1), p^2);
    c[11] := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), 4)*SOTRec.delta(2, p);
    c[12] := p*SOTRec.w((q - 1), p) + SOTRec.delta(2, p);
    c[13] := p*SOTRec.w((q - 1), p) - SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    c[14] := 2*SOTRec.w((q - 1), p) + SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    c[15] := (1 - SOTRec.delta(2, p))*2*SOTRec.w((q - 1), p);
    c[16] := SOTRec.w((p - 1), q);
    c[17] := (q + 1)*SOTRec.w((p - 1), q);
    c[18] := 1/2*(q + 3 - SOTRec.delta(2, q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    c[19] := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q);
    c[20] := 1/24*(q^3 + 7*q^2 + 21*q + 39 + 16*SOTRec.w((q - 1), 3) + 12*SOTRec.w((q - 1), 4))*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(2, q)) + 4*SOTRec.delta(2, q)
        + 1/4*(q + 5 + 2*SOTRec.w((q - 1), 4))*SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q))
        + SOTRec.w((p^2 + p +1), q)*(1 - SOTRec.delta(3, q))
        + SOTRec.w((p^2 + 1), q)*(1 - SOTRec.delta(2, q));
    c[21] := 1/2*(q + 3 - SOTRec.delta(2,q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    c[22] := SOTRec.w((p - 1), q);
    c[23] := (q + 1)*SOTRec.w((p - 1), q);
    c[24] := (q + 1)*SOTRec.w((p - 1), q) + SOTRec.delta(n, 3*2^4);;
    c[25] := SOTRec.w((p - 1), q);
    c[26] := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q) - SOTRec.delta(n, 3*2^4);
    c[27] := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    c[28] := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    c[29] := (q + 1)*SOTRec.w((p - 1), q);
    c[30] := SOTRec.w((p - 1), q);
    m := Sum(c);

    ### Info
    Print("The groups of order p^4q are solvable by Burnside's pq-Theorem.\n");
    Print("These groups are sorted by their Sylow subgroups.");
    Print("\>\>");
    SOTRec.Print(sot, "1 - ",c0, " are nilpotent and all Sylow subgroups are normal.");
    for i in [1..c0] do
        if c[i] = 1 then
            SOTRec.Print(sot, c0+Sum([1..i],x->c[x]),
            " is sovable, non-nilpotent and has a normal Sylow ", q, "-subgroup, with ", prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ".");
        elif c[i] > 1 then
            SOTRec.Print(sot, c0+1+Sum([1..i-1],x->c[x])," - ", c0+Sum([1..i],x->c[x]),
            " are sovable, non-nilpotent and have a normal Sylow ", q, "-subgroup, with ", prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ".");
        fi;
    od;
    for i in [1..15] do
        j := 15+i;
        if c[j] = 1 then
            SOTRec.Print(sot, c0+Sum([1..j],x->c[x]),
                " is sovable, non-nilpotent and has a normal ",  prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ", with cyclic Sylow ", q, "-subgroup.");
        elif c[j] > 1 then
            SOTRec.Print(sot, c0+1+Sum([1..j-1],x->c[x])," - ", c0+Sum([1..j],x->c[x]),
            " are sovable, non-nilpotent and have a normal ",  prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ", with cyclic Sylow ", q, "-subgroup.");
        fi;
    od;
    if n = 48 then
        SOTRec.Print(sot, "49 - 52 are solvable, non-nilpotent, and have no normal Sylow subgroups.");
    elif n = 1053 then
        SOTRec.Print(sot, "51 is solvable, non-nilpotent, and has no normal Sylow subgroups.");
    fi;
    Print("\<\<");
  end;

##############################################################################
SOTRec.infoPQRS := function(n, fac)
  local sot, c, p, q, r, s, m;
    sot := SOTRec.sot(n);
    c := [];
    p := fac[1][1];
    q := fac[2][1];
    r := fac[3][1];
    s := fac[4][1];

    ####
    Assert(1, s > r and r > q and q > p);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    Assert(1, IsPrimeInt(s));

    ##Cluster 1: Abelian group, Z(G) = G
    ##enumeration of each case by size of the centre
    c[1] := SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)
        + SOTRec.w((s - 1), p) + SOTRec.w((r - 1), p) + SOTRec.w((q - 1), p);
    c[2] := (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q) + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p) + SOTRec.w((r - 1), (p*q));
    c[3] := (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
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
    m := Sum(c);
    if m = 0 then
      Print("All groups of order ", n, " are abelian.\n");
    else
      Print("The groups of order pqrs are solvable and classified by O. H\"older.\n");
      Print("These groups are sorted by their centre.");
      Print("\>\>");
      SOTRec.Print(sot, "1 is abelian.");
      if c[1] = 1 then
        SOTRec.Print(sot, 1+c[1]," has centre of order that is a product of two distinct primes.");
      elif c[1] > 1 then
        SOTRec.Print(sot, "2 - ", 1+c[1], " have centre of order that is a product of two distinct primes.");
      fi;
      if c[2] = 1 then
        SOTRec.Print(sot, 1+c[1]+c[2]," has a cyclic centre of prime order.");
      elif c[2] > 1 then
        SOTRec.Print(sot, 2 + c[1], " - ", 1+c[1]+c[2], " have a cyclic centre of prime order.");
      fi;
      if c[3] = 1 then
        SOTRec.Print(sot, 1+m," has trivial centre.");
      elif c[2] > 1 then
        SOTRec.Print(sot, 2 + c[1]+c[2], " - ", 1+m, " have a trivial centre.");
      fi;
    fi;
    Print("\<\<");
  end;
