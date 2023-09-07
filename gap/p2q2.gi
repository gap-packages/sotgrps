## Groups of order p^2q^2 are solable by Burnside's pq-theorem.

## Let G be a group of order p^2q^2, then G has a normal Sylow subgroup unless |G| = 36, in which case the classification of G can be dealt with by direct computation.
## Let Q \in Syl_q(G), and P \in Syl_p(G). Since P and Q are abelian, G is nilpotent if and only if G is abelian, in which case the classification is given by FTFGAG.
## For non-nilpotent groups G with a normal Sylow subgroup, the classifcation of G follows from the classification of semidirect products Q \ltimes P and P \ltimes Q,
 ## where Q \in \{C_{q^2}, C_q^2\}, P \in \{C_{p^2}, C_p^2\}.
 ## For further details, see [2, Section 3.2 & 3.6].

############################################################################ all groups P2Q2
SOTRec.allGroupsP2Q2 := function(p, q)
local a, b, c, d, e, f, qq, ii, qqq, iii,
    s1, S1, s2, S2, r1, R1, r2, R2, all, list, G, k, t, matq, matq2, matp, matp2;;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    #### Cluster 0: abelian groups
    all := [ [ [p, p, q, q], [1, [2, 1]], [3, [4, 1]] ],
           [ [p, p, q, q], [3, [4, 1]] ],
           [ [p, p, q, q], [1, [2, 1]] ],
           [ [p, p, q, q], [2, [3, 1]] ] ];
    ## Computing roots
    a := Z(p); #\sigma_p
    b := Z(q); #\sigma_q

    #\sigma_{p^2}
    c := ZmodnZObj(Int(Z(p)), p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
        d := c;
    else
        d := c + 1;
    fi;

    #\sigma_{q^2}
    e := ZmodnZObj(Int(Z(q)), q^2);
    if not e^(q - 1) = ZmodnZObj(1, q^2) then
        f := e;
    else
        f := e + 1;
    fi;

    if (p - 1) mod q = 0 then
        #\rho(p, q)
        s1 := a^((p-1)/q);
        S1 := Int(s1);
        #\rho(p^2, q)
        r1 := d^(p*(p-1)/q);
        R1 := Int(r1);
        if (p - 1) mod (q^2) = 0 then
            #\rho(p, q^2)
            s2 := a^((p-1)/(q^2));
            S2 := Int(s2);
            #\rho(p^2, q)
            r2 := d^(p*(p-1)/(q^2));
            R2 := Int(r2);
        fi;
    fi;

    #### Cluster 1: ##C_{q^2} \ltimes C_{p^2}
    if (p - 1) mod q = 0 then
        ii := R1 mod p;
        qq := (R1 - ii)/p;
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);
        ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
        if (p - 1) mod q^2 = 0 then
            ii := R2 mod p;
            qq := (R2 - ii)/p;
            iii := R1 mod p;
            qqq := (R1 - iii)/p;
            Add(all, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ]);
        fi;
    fi;

    #### Cluster 2: C_q^2 \ltimes C_{p^2}
    if (p - 1) mod q = 0 then
        ii := R1 mod p;
        qq := (R1 - ii)/p;
        Add(all, [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);
    fi;

    #### Cluster 3: C_{q^2} \ltimes C_p^2 or C_9 \ltimes C_2^2
    if (p = 3 and q = 2) then
        matq := SOTRec.QthRootGL2P(2, 3);
        Add(all, [ [3, 3, 2, 2], [1, [2, 1]],
        [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;

    if (p - 1) mod q = 0 then
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S1]] ]);
        if q mod 2 = 1 then
            t := (q - 1)/2;
        else
            t := 0;
        fi;
        for k in [0..t] do
            Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S1]], [4, 1, [4, Int(a^(Int(b^k)*(p-1)/q))]] ]);
        od;

      if (p - 1) mod q^2 = 0 and q > 2 then
          Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S2]], [3, 2, [3, S1]] ]);
          for k in [0..(q^2 - q)/2] do
              Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S2]], [4, 1, [4, Int((a^(Int(f^k)*(p-1)/(q^2))))]], [3, 2, [3, S1]], [4, 2, [4, Int((a^(Int(f^k)*(p-1)/q)))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
          od;
          for k in [1..(q - 1)] do
              Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S2]], [3, 2, [3, S1]], [4, 1, [4, Int(a^(k*(p-1)/q))]] ]);
          od;
      fi;
      if (p - 1) mod q^2 = 0 and q = 2 then
          ii := Int(d^((p^2-p)/4)) mod p;
          qq := (Int(d^((p^2-p)/4)) - ii)/p;
          Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ]);
          Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
          Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^(3*(p - 1)/4))]], [4, 2, [4, p-1]] ]);
          Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
      fi;
  fi;
  if (p + 1) mod q = 0 and q mod 2 = 1 then
      matq := SOTRec.QthRootGL2P(p, q);
      Add(all, [ [q, q, p, p], [1, [2, 1]],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
  fi;
  if (p + 1) mod (q^2) = 0 then
      matq2 := SOTRec.QsquaredthRootGL2P(p, q);
      matq := matq2^q;
      Add(all, [ [q, q, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
        [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
        [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
    fi;

    #### Cluster 4: C_q^2 \ltimes C_p^2 or C_3 \ltimes C_2^2
    if (p - 1) mod q = 0 then
        Add(all, [ [q, q, p, p], [3, 1, [3, S1]] ]);
        if q mod 2 = 1 then
            t := (q - 1)/2;
        else
            t := 0;
        fi;

        for k in [0..t] do
            Add(all, [ [q, q, p, p], [3, 1, [3, S1]], [4, 1, [4, Int((a^(Int(b^k)*(p-1)/q)))]] ]);
        od;

        Add(all, [ [q, q, p, p], [3, 1, [3, S1]], [4, 2, [4, S1]] ]);

        if p = 3 and q = 2 then
            matq := SOTRec.QthRootGL2P(2, 3);
            Add(all, [ [3, 3, 2, 2],
            [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
        fi;
    fi;
    if (p + 1) mod q = 0 and q > 2 then
        matq := SOTRec.QthRootGL2P(p, q);
        Add(all, [ [q, q, p, p],
        [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] );
    fi;
    list := List(all, x -> SOTRec.groupFromData(x));
    return list;
end;
##
############################################################################
SOTRec.NumberGroupsP2Q2 := function(p, q)
local w;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    if p = 3 and q = 2 then
      w := 14;
    elif q = 2 then
      w := 11 + 5*SOTRec.w((p-1), 4) + SOTRec.w((p+1), 4);
    else
      w := 4 + (6+q)*SOTRec.w((p-1), q) + (4+q+q^2)*SOTRec.w((p-1), q^2)/2 + 2*SOTRec.w((p+1),q) + SOTRec.w((p+1), q^2);
    fi;
  return w;
end;


############################################################################
SOTRec.GroupP2Q2 := function(p, q, i)
local a, b, c, d, e, f, qq, ii, qqq, iii, l0, lst, G, k, t, matq, matq2, matp, matp2,
c1, c2, c3, c4, c5, s1, S1, s2, S2, r1, R1, r2, R2;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    #### case1: q nmid (p-1), q nmid (p^2 -1), q > 2
    l0 := [ [ [p, p, q, q], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, q, q], [3, [4, 1]] ], [ [p, p, q, q], [1, [2, 1]] ], [ [p, p, q, q], [2, [3, 1]] ] ];
    if i < 5 then
        return SOTRec.groupFromData(l0[i]);
    fi;
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

    if (p - 1) mod q = 0 then
        #\rho(p, q)
        s1 := a^((p-1)/q);
        S1 := Int(s1);

        #\rho(p^2, q)
        r1 := d^(p*(p-1)/q);
        R1 := Int(r1);

        if (p - 1) mod (q^2) = 0 then
            #\rho(p, q^2)
            s2 := a^((p-1)/(q^2));
            S2 := Int(s2);

            #\rho(p^2, q)
            r2 := d^(p*(p-1)/(q^2));
            R2 := Int(r2);
        fi;
    fi;

    #### Enumeration
    c1 := SOTRec.w((p - 1), q) + SOTRec.w((p - 1), q^2);
    c2 := SOTRec.w((p - 1), q);
    c3 := 1/2*(q + 3 - SOTRec.w(2, q))*SOTRec.w((p - 1), q) + 1/2*(q^2 + q + 2)*SOTRec.w((p - 1), q^2) + (1 - SOTRec.w(2, q))*SOTRec.w((p + 1), q) + SOTRec.w((p + 1), q^2) + SOTRec.delta(p^2*q^2, 36);
    c4 := 1/2*(q + 5 - SOTRec.w(2, q))*SOTRec.w((p - 1), q) + (1 - SOTRec.w(2, q))*SOTRec.w((p + 1), q) + SOTRec.delta(p^2*q^2, 36);
    #### Cluster 1: ##C_{q^2} \ltimes C_{p^2}
    if i > 4 and i < 5 + c1 then
        lst := [];

        if (p - 1) mod q = 0 then
            ii := R1 mod p;
            qq := (R1 - ii)/p;
            Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);
            ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
            if (p - 1) mod q^2 = 0 then
                ii := R2 mod p;
                qq := (R2 - ii)/p;
                iii := R1 mod p;
                qqq := (R1 - iii)/p;
                Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ]);
            fi;
        fi;
        return SOTRec.groupFromData(lst[i - 4]);

    #### Cluster 2: C_q^2 \ltimes C_{p^2}
    elif i > 4 + c1 and i < 5 + c1 + c2 then
        lst := [];
        if (p - 1) mod q = 0 then
            ii := R1 mod p;
            qq := (R1 - ii)/p;
            Add(lst, [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);
        fi;
        return SOTRec.groupFromData(lst[i - 4 -c1]);

    #### Cluster 3: C_{q^2} \ltimes C_p^2
    elif i > 4 + c1 + c2 and i < 5 + c1 + c2 + c3 then
        lst := [];
        if p = 3 and q = 2 then ## ! C_{p^2} \ltimes C_q^2
            matq := SOTRec.QthRootGL2P(2, 3);
            Add(lst, [ [3, 3, 2, 2], [1, [2, 1]],
            [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
        fi;

        if (p - 1) mod q = 0 then
            Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S1]] ]);

            if q mod 2 = 1 then
                t := (q - 1)/2;
            else
                t := 0;
            fi;
            for k in [0..t] do
                Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S1]], [4, 1, [4, Int(a^(Int(b^k)*(p-1)/q))]] ]);
            od;

            if (p - 1) mod q^2 = 0 and q > 2 then
                Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/(q^2)))]], [3, 2, [3, Int(a^((p - 1)/q))]] ]);
                for k in [0..(q^2 - q)/2] do
                    Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S2]], [4, 1, [4, Int((a^(Int(f^k)*(p-1)/(q^2))))]], [3, 2, [3, S1]], [4, 2, [4, Int((a^(Int(f^k)*(p-1)/q)))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
                od;
                for k in [1..(q - 1)] do
                    Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, S2]], [3, 2, [3, S1]], [4, 1, [4, Int(a^(k*(p-1)/q))]] ]);
                od;
            fi;
            if (p - 1) mod q^2 = 0 and q = 2 then
                ii := Int(d^((p^2-p)/4)) mod p;
                qq := (Int(d^((p^2-p)/4)) - ii)/p;
                Add(lst, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ]);
                Add(lst, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
                Add(lst, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^(3*(p - 1)/4))]], [4, 2, [4, p-1]] ]);
                Add(lst, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
            fi;
        fi;
        if (p + 1) mod q = 0 and q mod 2 = 1 then
            matq := SOTRec.QthRootGL2P(p, q);
            Add(lst, [ [q, q, p, p], [1, [2, 1]],
            [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
        fi;
        if (p + 1) mod (q^2) = 0 then
            matq2 := SOTRec.QsquaredthRootGL2P(p, q);
            matq := matq2^q;
            Add(lst, [ [q, q, p, p], [1, [2, 1]],
            [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
            [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
            [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
        fi;
        return SOTRec.groupFromData(lst[i - 4 - c1 - c2]);

    #### Cluster 4: C_q^2 \ltimes C_p^2
    elif i > 4 + c1 + c2 + c3 and i < 5 + c1 + c2 + c3 + c4 then
        lst := [];
        if (p - 1) mod q = 0 then
            Add(lst, [ [q, q, p, p], [3, 1, [3, S1]] ]);
            if q mod 2 = 1 then
                t := (q - 1)/2;
            else
                t := 0;
            fi;
            for k in [0..t] do
                Add(lst, [ [q, q, p, p], [3, 1, [3, S1]], [4, 1, [4, Int((a^(Int(b^k)*(p-1)/q)))]] ]);
            od;
            Add(lst, [ [q, q, p, p], [3, 1, [3, S1]], [4, 2, [4, S1]] ]);

            if p = 3 and q = 2 then
                matq := SOTRec.QthRootGL2P(2, 3);
                Add(lst, [ [3, 3, 2, 2],
                [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
                [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
            fi;
        fi;
        if (p + 1) mod q = 0 and q > 2 then
            matq := SOTRec.QthRootGL2P(p, q);
            Add(lst, [ [q, q, p, p],
            [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] );
        fi;
        return SOTRec.groupFromData(lst[i - 4 - c1 - c2 - c3]);
    fi;
end;
############################################################################
