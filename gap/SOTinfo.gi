SOTRec.infoP2Q2 := function(n)
  local fac, p, q, c, m, prop, i;
    fac := Factors(n);
    if not List(Collected(fac), x->x[2]) = [2, 2] then
      Error("Argument must be of the form of p^2q^2"); fi;
    q := fac[1];
    p := fac[4];
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
    Print("\n  There are ", m + 4, " groups of order ", n,".\n");
    Print("\n  The groups of order p^2q^2 are solvable by Burnside's pq-Theorem.\n");
    Print("  These groups are sorted by their Sylow subgroups.\n");
    Print(SOTRec.sot, "1 - 4 are abelian and all Sylow subgroups are normal.\n");
    if n = 36 then
      Print(SOTRec.sot, "5 is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[1][2], ", and Sylow ", q, "-subgroup ", prop[1][1], ".\n");
      Print(SOTRec.sot, "6 is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[2][2], ", and Sylow ", q, "-subgroup ", prop[2][1], ".\n");
      Print(SOTRec.sot, "7 is non-abelian, non-nilpotent and has a normal Sylow 2-subgroup [4, 2], and Sylow 3-subgroup [9, 1].\n");
      Print(SOTRec.sot, "8 - 10 are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[3][2], ", and Sylow ", q, "-subgroup ", prop[3][1], ".\n");
      Print(SOTRec.sot, "11 - 14 are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[3][2], ", and Sylow ", q, "-subgroup ", prop[3][1], ".\n");
    else
      for i in [1..4] do
        if c[i] = 1 then
          Print(SOTRec.sot, 4+Sum([1..i],x->c[x]), " is non-abelian, non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[i][2], ", and Sylow ", q, "-subgroup ", prop[i][1], ".\n");
        elif c[i] > 1 then
          Print(SOTRec.sot, 5+Sum([1..i-1],x->c[x])," - ", 4+Sum([1..i],x->c[x]),
          " are non-abelian, non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[i][2], ", and Sylow ", q, "-subgroup ", prop[i][1], ".\n");
        fi;
      od;
    fi;
  end;
##############################################################################
SOTRec.infoP3Q := function(n)
  local fac, p, q, c, m, prop, i;
    fac := Factors(n);
    if not List(Collected(fac), x->x[2]) in [ [1, 3], [3, 1] ] then
      Error("Argument must be of the form of p^3q"); fi;
    p := fac[2];
    if fac[1] = fac[2] then
    q := fac[4]; elif fac[3] = fac[4] then
    q := fac[1]; fi;
    prop := [[p^3, 1], [p^3, 2], [p^3, 5], [p^3, 3], [p^3, 4],
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

    Print("\n  There are ", m + 5, " groups of order ", n,".\n");
    Print("\n  The groups of order p^3q are solvable by Burnside's pq-Theorem.\n");
    Print("  These groups are sorted by their Sylow subgroups.\n");
    Print(SOTRec.sot, "1 - 3 are abelian.\n");
    Print(SOTRec.sot, "4 - 5 are nonabelian nilpotent and have a normal Sylow ", p,"-subgroup and a normal Sylow ", q, "-subgroup.\n");
    for i in [1..5] do
      if c[i] = 1 then
        Print(SOTRec.sot, 5+Sum([1..i],x->c[x])," is non-nilpotent and has a normal Sylow ", p, "-subgroup ", prop[i], ".\n");
      elif c[i] > 1 then
        Print(SOTRec.sot, 6+Sum([1..i-1],x->c[x])," - ", 5+Sum([1..i],x->c[x]),
        " are non-nilpotent and have a normal Sylow ", p, "-subgroup ", prop[i], ".\n");
      fi;
    od;
    for i in [6..10] do
      if c[i] = 1 then
        Print(SOTRec.sot, 5+Sum([1..i],x->c[x])," is non-nilpotent and has a normal Sylow ", q, "-subgroup ", [q, 1], " with Sylow ", p, "-subgroup ", prop[i], ".\n");
      elif c[i] > 1 then
        Print(SOTRec.sot, 6+Sum([1..i-1],x->c[x])," - ", 5+Sum([1..i],x->c[x])," are non-nilpotent and have a normal Sylow ", q, "-subgroup ", [q, 1], " with Sylow ", p, "-subgroup ", prop[i], ".\n");
      fi;
    od;
    if c[11] = 1 then
      Print(SOTRec.sot, "15 is non-nilpotent, isomorphic to Sym(4), and has no normal Sylow subgroups.\n");
    fi;
  end;
##############################################################################
SOTRec.infoP2QR := function(n)
  local fac, primefac, p, q, r, m, c, fit, i;
    c := [];
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 3 then
      Error("Argument must be of the form of p^2qr"); fi;
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
      Print("\n  There are 2 groups of order ", n,".\n");
      Print("\n  All groups of order ", n, " are abelian.\n");
    else
      Print("\n  There are ", m + 2, " groups of order ", n,".\n");
      Print("\n  The groups of order p^2qr are either solvable or isomorphic to Alt(5).\n");
      Print("  The solvable groups are sorted by their Fitting subgroup. \n");
      Print(SOTRec.sot, "1 - 2 are the nilpotent groups.\n" );
      for i in [1..7] do
        if c[i] = 1 then
          Print(SOTRec.sot, 2+Sum([1..i],x->c[x])," has Fitting subgroup of order ", fit[i], ".\n");
        elif c[i] > 1 then
          Print(SOTRec.sot, 3+Sum([1..i-1],x->c[x])," - ", 2+Sum([1..i],x->c[x]), " have Fitting subgroup of order ", fit[i], ".\n");
        fi;
      od;
      if n = 60 then
        Print(SOTRec.sot, "13 is nonsolvable and has Fitting subgroup of order 1.\n");
      fi;
    fi;
  end;
##############################################################################
SOTRec.infoP4Q := function(n)
    local fac, LF, p, q, c, c0, m, prop, i, j;
    fac := Collected(Factors(n));
    LF := List(fac, x -> x[2]);
    if not LF in [ [1, 4], [4, 1] ] then
        Error("Argument must be of the form of p^4q.");
    elif LF = [1, 4] then
        p := fac[2][1]; q := fac[1][1];
    elif LF = [4, 1] then
        p := fac[1][1]; q := fac[2][1];
    fi;
    prop := [];
    if p > 3 then
        prop[1] := ["sovable, non-nilpotent", "cylic", [p^4, 1]];
        prop[2] := ["sovable, non-nilpotent", "abelian", [p^4, 5]];
        prop[3] := ["sovable, non-nilpotent", "abelian", [p^4, 2]];
        prop[4] := ["sovable, non-nilpotent", "abelian", [p^4, 11]];
        prop[5] := ["sovable, non-nilpotent", "elementary abelian", [p^4, 15]];
        prop[6] := ["sovable, non-nilpotent", "nonabelian", [p^4, 14]];
        prop[7] := ["sovable, non-nilpotent", "nonabelian", [p^4, 6]];
        prop[8] := ["sovable, non-nilpotent", "nonabelian", [p^4, 13]];
        prop[9] := ["sovable, non-nilpotent", "nonabelian", [p^4, 3]];
        prop[10] := ["sovable, non-nilpotent", "nonabelian", [p^4, 4]];
        prop[11] := ["sovable, non-nilpotent", "nonabelian", [p^4, 12]];
        prop[12] := ["sovable, non-nilpotent", "nonabelian", [p^4, 9]];
        prop[13] := ["sovable, non-nilpotent", "nonabelian", [p^4, 10]];
        prop[14] := ["sovable, non-nilpotent", "nonabelian", [p^4, 7]];
        prop[15] := ["sovable, non-nilpotent", "nonabelian", [p^4, 8]];
    elif p = 3 then
        prop[1] := ["sovable, non-nilpotent", "cylic", [81, 1]];
        prop[2] := ["sovable, non-nilpotent", "abelian", [81, 5]];
        prop[3] := ["sovable, non-nilpotent", "abelian", [81, 2]];
        prop[4] := ["sovable, non-nilpotent", "abelian", [81, 11]];
        prop[5] := ["sovable, non-nilpotent", "elementary abelian", [81, 15]];
        prop[6] := ["sovable, non-nilpotent", "nonabelian", [81, 14]];
        prop[7] := ["sovable, non-nilpotent", "nonabelian", [81, 6]];
        prop[8] := ["sovable, non-nilpotent", "nonabelian", [81, 13]];
        prop[9] := ["sovable, non-nilpotent", "nonabelian", [81, 3]];
        prop[10] := ["sovable, non-nilpotent", "nonabelian", [81, 4]];
        prop[11] := ["sovable, non-nilpotent", "nonabelian", [81, 12]];
        prop[12] := ["sovable, non-nilpotent", "nonabelian", [81, 8]];
        prop[13] := ["sovable, non-nilpotent", "nonabelian", [81, 9]];
        prop[14] := ["sovable, non-nilpotent", "nonabelian", [81, 7]];
        prop[15] := ["sovable, non-nilpotent", "nonabelian", [81, 10]];
    elif p = 2 then
        prop[1] := ["sovable, non-nilpotent", "cylic", [16, 1]];
        prop[2] := ["sovable, non-nilpotent", "abelian", [16, 5]];
        prop[3] := ["sovable, non-nilpotent", "abelian", [16, 2]];
        prop[4] := ["sovable, non-nilpotent", "abelian", [16, 10]];
        prop[5] := ["sovable, non-nilpotent", "elementary abelian", [16, 14]];
        prop[6] := ["sovable, non-nilpotent", "nonabelian", [16, 13]];
        prop[7] := ["sovable, non-nilpotent", "nonabelian", [16, 11]];
        prop[8] := ["sovable, non-nilpotent", "nonabelian", [16, 3]];
        prop[9] := ["sovable, non-nilpotent", "nonabelian", [16, 12]];
        prop[10] := ["sovable, non-nilpotent", "nonabelian", [16, 4]];
        prop[11] := ["sovable, non-nilpotent", "nonabelian", [16, 6]];
        prop[12] := ["sovable, non-nilpotent", "nonabelian", [16, 8]];
        prop[13] := ["sovable, non-nilpotent", "nonabelian", [16, 7]];
        prop[14] := ["sovable, non-nilpotent", "nonabelian", [16, 9]];
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
    Print("\n  There are ", m + c0, " groups of order ", n,".\n");
    Print("\n  The groups of order p^4q are solvable by Burnside's pq-Theorem.\n");
    Print("  These groups are sorted by their Sylow subgroups.\n");
    Print(SOTRec.sot, "1 - ",c0, " are nilpotent and all Sylow subgroups are normal.\n");
    for i in [1..c0] do
        if c[i] = 1 then
            Print(SOTRec.sot, c0+Sum([1..i],x->c[x]),
            " is ", prop[i][1], "and has a normal Sylow ", q, "-subgroup,", "\n         with ", prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ".\n");
        elif c[i] > 1 then
            Print(SOTRec.sot, c0+1+Sum([1..i-1],x->c[x])," - ", c0+Sum([1..i],x->c[x]),
            " are ", prop[i][1], "and have a normal Sylow ", q, "-subgroup,", "\n         with ", prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ".\n");
        fi;
    od;
    for i in [1..15] do
        j := 15+i;
        if c[j] = 1 then
            Print(SOTRec.sot, c0+Sum([1..j],x->c[x]),
                " is ", prop[i][1], "and has a normal ",  prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ",\n         with cyclic Sylow ", q, "-subgroup ", ".\n");
        elif c[j] > 1 then
            Print(SOTRec.sot, c0+1+Sum([1..j-1],x->c[x])," - ", c0+Sum([1..j],x->c[x]),
            " are ", prop[i][1], "and have a normal ",  prop[i][2], " Sylow ", p, "-subgroup ", prop[i][3], ",\n         with cyclic Sylow ", q, "-subgroup ", ".\n");
        fi;
    od;
    if n = 48 then
        Print(SOTRec.sot, "49 - 52 are solvable, non-nilpotent, and have no normal Sylow subgroups.\n");
    elif n = 1053 then
        Print(SOTRec.sot, "51 is solvable, non-nilpotent, and has no normal Sylow subgroups.\n");
    fi;
  end;

##############################################################################
SOTRec.infoPQRS := function(n)
  local c, fac, p, q, r, s, m;
    c := [];
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
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
      Print("\n  There is 1 group of order ", n,".\n");
      Print("\n  All groups of order ", n, " are abelian.\n");
    else
      Print("\n  There are ", m + 1, " groups of order ", n,".\n");
      Print("\n  The groups of order pqrs are solvable and classified by O. H\"older.\n");
      Print("  These groups are sorted by their centre. \n");
      Print(SOTRec.sot, "1 is abelian.\n");
      if c[1] = 1 then
        Print(SOTRec.sot, 1+c[1]," has centre of order that is a product of two distinct primes.\n");
      elif c[1] > 1 then
        Print(SOTRec.sot, "2 - ", 1+c[1], " have centre of order that is a product of two distinct primes.\n");
      fi;
      if c[2] = 1 then
        Print(SOTRec.sot, 1+c[1]+c[2]," has a cyclic centre of prime order.\n");
      elif c[2] > 1 then
        Print(SOTRec.sot, 2 + c[1], " - ", 1+c[1]+c[2], " have a cyclic centre of prime order.\n");
      fi;
      if c[3] = 1 then
        Print(SOTRec.sot, 1+m," has trivial centre.\n");
      elif c[2] > 1 then
        Print(SOTRec.sot, 2 + c[1]+c[2], " - ", 1+m, " have a trivial centre.\n");
      fi;
    fi;
  end;
