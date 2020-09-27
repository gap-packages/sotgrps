##Construct all groups of order p^4q: all such groups are solvable.
##The isomorphism types of nilpotent groups of such order are in one-to-one correspondence with the isomorphism type of the Sylow p-subgroup. In particular, such groups are stored by "lowpowerPGroups".
##It remains to investigate the nonnilpotent groups. There are three classes of such groups: one class where the Sylow p-subgroup is normal, one where the Sylow q-subgroup is normal, and one with no normal Sylow subgroups.
###################################################################
msg.allGroupsP4Q := function(n)
  local fac, p, q, all, list, a, b, c, d, e, f, g, h, r1, r2, r3, r4, s1, s2, s3, s4, u, v, x, y,
        R1, R2, R3, R4, S1, S2, S3, S4, matGL2, matGL3, matGL4, funci, funcii, k, j, l,
        c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
        c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30;
    fac := Collected(Factors(n));
    if not List(fac, x -> x[2]) in [ [4, 1], [1, 4] ] then
      Error("Argument must be of the form of p^4q");
    elif List(fac, x -> x[2]) = [1, 4] then p := fac[2][1]; q := fac[1][1];
    else p := fac[1][1]; q := fac[2][1];
    fi;

    a := Z(p);
    b := Z(q);
    if (q - 1) mod p = 0 then
      r1 := b^((q-1)/p);
      R1 := Int(r1);
    fi;
    if (q - 1) mod (p^2) = 0 then
      r2 := b^((q-1)/(p^2));
      R2 := Int(r2);
    fi;
    if (q - 1) mod (p^3) = 0 then
      r3 := b^((q-1)/(p^3));
      R3 := Int(r3);
    fi;
    if (q - 1) mod (p^4) = 0 then
      r4 := b^((q-1)/(p^4));
      R4 := Int(r4);
    fi;
    ##construct all nilpotent groups:
    all := [];
    for i in msg.lowpowerPGroups(p, 4, 0) do
      Add(i[1], q);
      Add(all, i);
    od;

    ##Class 1: Group G is solvable, nonnilpotent. Sylow p-subgroup is normal in G. Thus G \cong C_q \ltimes P is a nonabelian split extension.
    ##Isomorphism types of such groups are in one-to-one correspondence with the conjugacy classes of cyclic subgroups of order q in \Aut P.

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    #1 P \cong C_{p^4}
    c1 := msg.w((q - 1), p) + msg.w((q - 1), p^2) + msg.w((q - 1), p^3) + msg.w((q - 1), p^4);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]);
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]);
      fi;
      if (q - 1) mod p^3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]);
      fi;
      if (q - 1) mod p^3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R4]], [5, 2, [5, R3]], [5, 3, [5, R2]], [5, 4, [5, R1]] ]);
      fi;
    fi;

    #2 P \cong C_{p^3} \times C_p
    c2 := 2*msg.w((q - 1), p) + 2*msg.w((q - 1), p^2) + msg.w((q - 1), p^3);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 4, [5, R1]] ]); #Z(G) \cong C_{p^3}
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2}
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
      fi;
      if (q - 1) mod p^3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #Z(G) \cong C_p
      fi;
    fi;

    #3 P \cong C_{p^2} \times C_{p^2}
    c3 := msg.w((q - 1), p) + msg.w((q - 1), p^2);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      fi;
    fi;

    #4 P \cong C_{p^2} \times C_p^2
    c4 := 2*msg.w((q - 1), p) + msg.w((q - 1), p^2);
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 3, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
    fi;
    if (q - 1) mod p^2 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
    fi;

    #5 P \cong C_p^4
    c5 := msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
      fi;
    fi;

    #6 P \cong [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ]
    c6 := 3*msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        Add(all, [ [p, p, p, p, q], [2, [4, 1]], [3, 1, [3, 1, 4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong p_- \times C_q
      fi;
    fi;

    #7 P \cong [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ]
    c7 := p*msg.w((q - 1), p) + p*msg.w((q - 1), p^2);
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^3} \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      fi;
      if (q - 1) mod p^2 = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r2^k)]], [5, 2, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^2} \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
      fi;
    fi;

    #8 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    c8 := (p + 1)*msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_- \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      fi;
    fi;

    #9 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ]
    c9 := 2*msg.w((q - 1), p) + msg.w((q - 1), p^2);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
      fi;
    fi;

    #10 P \cong [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    c10 := p*msg.w((q - 1), p) + (p - 1)*msg.w((q - 1), p^2);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
      fi;
      if (q - 1) mod p^2 = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r2^k)]], [5, 4, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^2} \times C_q
        od;
      fi;
    fi;

    #11 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ]
    c11 := 2*msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      fi;
    fi;

    #12 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ]
    c12 := p*msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..(p - 1)/2] do
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        if p > 3 then
          for k in [1..(p - 1)/2] do
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong p_- \times C_q
          od;
        else
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, p - 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, p - 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong 3_- \times C_q
        fi;
      fi;
    fi;

    #13 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ]
    c13 := p*msg.w((q - 1), p);
    if p > 3 and (q - 1) mod p = 0 then
      for k in [1..(p - 1)/2] do
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      od;
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      for k in [1..(p - 1)/2] do
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong p_- \times C_q
      od;
    elif p = 3 and (q - 1) mod 3 = 0 then
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
    fi;


    #14 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ]
    c14 := 2*msg.w((q - 1), p);
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      fi;
      if p = 3 and (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]);
      fi;
    fi;

    #15 P \cong [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] if p > 3,
    #or P \cong [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] if p = 3
    c15 := 2*msg.w((q - 1), p);
    if p > 3 and (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
    fi;
    if p = 3 and (q - 1) mod 3 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_- \times C_q
    fi;

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    if (p - 1) mod q = 0 then
      if not Int(a)^(p - 1) mod p^2 = 1 then
        c := ZmodnZObj(Int(a), p^2);
        d := ZmodnZObj(Int(a), p^3);
        e := ZmodnZObj(Int(a), p^4);
      else
        c := ZmodnZObj(Int(a) + p, p^2);
        d := ZmodnZObj(Int(a) + p, p^3);
        e := ZmodnZObj(Int(a) + p, p^4);
      fi;
      s1 := a^((p - 1)/q);;
      s2 := c^((p^2 - p)/q);;
      s3 := d^((p^3 - p^2)/q);;
      s4 := e^((p^4 - p^3)/q);;
      S1 := Int(s1);;
      S2 := Int(s2);;
      S3 := Int(s3);;
      S4 := Int(s4);;
    fi;
    #1 P \cong C_{p^4}
    c16 := msg.w((p - 1), q);
    if p > 2 and (p - 1) mod q = 0 then
      u := S4 mod p;
      v := (S4 - u)/p mod p;
      x := ((S4 - u)/p - v)/p mod p;
      y := (((S4 - u)/p - v)/p - x)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v, 4, x, 5, y]], [3, 1, [3, u, 4, v, 5, x]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #unique
    fi;

    #2 P \cong C_{p^3} \times C_p
    c17 := (p + 1)*msg.w((p - 1), q);
    if p > 2 and (p - 1) mod q = 0 then
      u := S3 mod p;
      v := (S3 - u)/p mod p;
      x := ((S3 - u)/p - v)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_{p^3}
      for i in [1..(q - 1)] do
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, Int(s1^k)]] ]); #Z(G) = 1
      od;
    fi;

    #3 P \cong C_{p^2} \times C_{p^2}
    c18 := p*msg.w((p - 1), q);
    if p > 2 and (p - 1) mod q = 0 then
      u := S2 mod p;
      v := (S2 - u)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]] ]); #Z(G) \cong C_{p^2}
      for k in [1..(q - 1)] do
        x := Int(s2^k) mod p;
        y := (Int(s2^k) - x)/p;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]]. [4, 1, [4, x, 5, y]], [5, 1, [5, x]] ]); #Z(G) = 1
      od;
    fi;

    #4 P \cong C_{p^2} \times C_p^2
    if p > 2 and (p - 1) mod q = 0 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]] ]); #Z(G) \cong C_p \times C_{p^2}
      for k in [0..(q - 1)/2)] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]] ]); #Z(G) \cong C_{p^2}
      od;
      Add(all, [ [q, p, p, p, p], [4, [5, 1]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) \cong C_p^2
      for k in [1..(q - 1)] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) \cong C_p
      od;
      for k in [0..(q - 1)/2] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) = 1
      od;
      for k in [2..q - 1] do
        x := Int(s2^k) mod p;
        y := (Int(s2^k) - x)/p;
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, x, 5, y]], [5, 1, [5, x]] ]);
      od;
    fi;

    #5 P \cong C_p^4
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]] ]); #Z(G) \cong C_p^3, G \cong (C_q \ltimes C_p) \times C_p^3
      for k in [0..(q - 1)/2] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^Int(b^k))]] ]); #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
      od;
      #below Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
      if q = 2 then
        Add(all, [ [q, p, p ,p, p], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1)]], [4, 1, [4, (p - 1)]] ]);
      elif q = 3 then
        for k in [0, 1] do
          Add(l8, [ [q, p, p ,p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
        od;
      else #q > 3
        for k in Filtered([1..(q - 2)], x-> not x = (q - 1)/2) do
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
        od;
        if q mod 3 = 1 then
          for k in [0..(q - 1)/2]
            do Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, Int(s1^(Int(b^(-k))))]] ]);
          od;
        else #q mod 3 = 2 and q > 2
          for k in [0..(q - 1)/2]
            do Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, Int(s1^(Int(b^(-k))))]] ]);
          od;
        fi;
        func := function(q)
          local i, j, k, ll;
          ll := [];
          for i in [1..Int((q - 3)/3)] do
            for j in [i + 1..Int((q - 1 - i)/2)] do
              if ((q - 1 - i - j) mod (q - 1) <> i) and ((q - 1 - i - j) mod (q - 1) <> j) and (-i) mod (q - 1) <> j then
                Add(ll, [(-i) mod (q - 1), j]);
                Add(ll, [(-i) mod (q - 1), (q - 1 - i - j)]);
              fi;
            od;
          od;
          return ll;
        end;
        #explength := 1/6*(q^2 - 8*q + 15 + 4*msg.w((q - 1), 3));
        for k in func(q) do
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]] ]);
        od;
      fi;
      #below: Z(G) = 1, G \cong C_q \ltimes C_p^4
      for k in [0..(q - 2)] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, S1]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
      od;
      for k in [1..(q - 1)/2] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
      od;
      for k in [1..(q - 2)] do
        for l in [k + 1..(q - 2)] do 
          if l > k then
            Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^l)))]] ]);
          fi;
        od;
      od;

    elif (p + 1) mod q = 0 and q > 2 then #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
      matGL2 := msg.QthRootGL2P(p, q);;
      Add(all, [ [q, p, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
    elif (p^2 + p + 1 ) mod q = 0 and q > 3 then #Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
      matGL3 := msg.QthRootGL3P(p, q);
      Add(all, [ [q, p, p, p, p],
      [2, 1, [2, Int(matGL3[1][1]), 3, Int(matGL3[2][1]), 4, Int(matGL3[3][1])]],
      [3, 1, [2, Int(matGL3[1][2]), 3, Int(matGL3[2][2]), 4, Int(matGL3[3][2])]],
      [4, 1, [2, Int(matGL3[1][3]), 3, Int(matGL3[2][3]), 4, Int(matGL3[3][3])]] ]);
    fi;



    #list := List(all, x -> msg.groupFromData(x));
  return all;
end;
