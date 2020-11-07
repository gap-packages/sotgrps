############################################################################
msg.allGroupsP3Q := function(n)
  local fac, p, q, all, list, a, b, c, d, e, f, r1, r2, r3, s1, s2, s3, s, ii, qq, iii, qqq, matGL2, matGL3, func, k;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
      Error("Argument must be of the form of p^3q"); fi;
    p := fac[2];
    if fac[1] = fac[2] then
    q := fac[4]; elif fac[3] = fac[4] then
    q := fac[1]; fi;
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
############ add abelian groups in:
    all := [ [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, q], [1, [2, 1]] ], [ [p, p, p, q] ] ];
############ case 1: no normal Sylow subgroup -- necessarily n = 24
    if n = 24 then
      Add(all, [ [2, 3, 2, 2], [2, 1, [2, 2]], [3, 1, [4, 1]], [3, 2, [4, 1]], [4, 1, [3, 1]], [4, 2, [3, 1, 4, 1]] ]);
    fi;

############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
    if p > 2 then
      Append(all, [ [ [p, p, p, q], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p, q], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ]);
    else
      Append(all, [ [ [2, 2, 2, q], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ]);
    fi;

############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
    ## class 1: when P = C_{p^3}
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_p
    fi;
    if (q - 1) mod (p^2) = 0 then
      Add(all, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r2)]], [4, 2, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_{p^2}
    fi;
    if (q - 1) mod (p^3) = 0 then
      Add(all, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r3)]], [4, 2, [4, Int(r2)]], [4, 3, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_{p^3}
    fi;
    ## class 2: when P = C_{p^2} \times C_p, there are at most two isom types of semidirect products of P \ltimes Q
    if (q - 1) mod p = 0 then
      Append(all, [ [ [p, p, p, q], [1, [2, 1]], [4, 3, [4, Int(r1)]] ], [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, Int(r1)]] ] ]);
    fi;
    if (q - 1) mod (p^2) = 0 then
      Add(all, [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, Int(r2)]], [4, 2, [4, Int(r1)]] ]);
    fi;
    ## class 3: when P is elementary abelian, there is at most one isom type of P \ltimes Q
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, q], [4, 1, [4, Int(r1)]] ]);
    fi;
    ## class 4: when P is extraspecial + type, there is at most one isom type of P \ltimes Q
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [4, Int(r1)]] ]);
    fi;
    if p = 2 then
      Add(all, [ [2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q - 1]] ]);
    fi;
    ## class 5: when P is extraspecial - type, there are at most p isom types of P \ltimes Q
    if (q - 1) mod p = 0 and p > 2 then
      for k in [1..p - 1] do
        Add(all, [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, Int(r1^k)]] ]);
      od;
      Add(all, [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 2, [4, Int(r1)]] ]);
    fi;
    ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
    if p = 2 and q > p then
      Add(all, [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q - 1]] ]);
    fi;

############ case 4: nonabelian and only the Sylow p-subgroup is normal
    if (p - 1) mod q = 0 then
      s1 := a^((p - 1)/q);

      if not Int(a)^(p - 1) mod p^2 = 1 then
        c := ZmodnZObj(Int(a), p^2);
        d := ZmodnZObj(Int(a), p^3);
      else
        c := ZmodnZObj(Int(a) + p, p^2);
        d := ZmodnZObj(Int(a) + p, p^3);
      fi;

      s2 := c^((p^2-p)/q);
      iii := Int(s2) mod p;
      qqq := (Int(s2) - iii)/p;

      s3 := d^((p^3 - p^2)/q);
      s := Int(s3) mod p;
      ii := (Int(s3) - s)/p mod p;
      qq := ((Int(s3) - s)/p - ii)/p;
    fi;

    ## class 1: when P is cyclic, there is at most isom type of semidirect products of Q \ltimes P
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, s, 3, ii, 4, qq]], [3, 1, [3, s, 4, ii]], [4, 1, [4, s]] ]);
    fi;
    ## class 2: when P = C_{p^2} \times C_p, there are at most (q + 1) isomorphism types of Q \ltimes P
    if (p - 1) mod q = 0 then
      Append(all, [ [ [q, p, p, p], [3, [4, 1]], [2, 1, [2, Int(s1)]] ], ## (C_q \ltimes C_p) \times C_{p^2}
      [ [q, p, p, p], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ] ]); ## (C_q \ltimes C_{p^2}) \times C_p
      for k in [1..(q - 1)] do
        Add(all, [ [q, p, p, p], [ 2, [3, 1]], [2, 1, [2, (Int(s2) mod p), 3, ((Int(s2) - (Int(s2) mod p))/p)]], [3, 1, [3, (Int(s2) mod p)]], [4, 1, [4, Int(s1^k)]] ]); ## C_q \ltimes (C_{p^2} \times C_p)
      od;
    fi;
    ## class 3: when P is elementary abelian
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p], [4, 1, [4, Int(s1)]] ]); ## C_q \ltimes C_p \times C_p^2
    fi;
    if (p - 1) mod q = 0 and q > 2 then
      for k in [0..(q - 1)/2] do
        Add(all, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^k)))]] ]); ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
      od;
    fi;
    if q = 2 then
      Add(all, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]] ]);
    fi;

    if (p + 1) mod q = 0 and q > 2 then
      matGL2 := msg.QthRootGL2P(p, q);;
      Add(all, [ [q, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]); ## (C_q \ltimes C_p^2) \times C_p when q | (p + 1)
    fi;

    ## below: (C_q \ltimes C_p^3) when q | (p - 1)
    if q = 2 then
      Add(all, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1)]] ]);
    fi;
    if (p - 1) mod 3 = 0 and q = 3 then
      for k in [0, 1] do
        Add(all, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q > 3 then
      for k in Filtered([1..(q - 2)], x-> not x = (q - 1)/2) do
        Add(all, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q mod 3 = 1 then
      for k in [0..(q - 1)/2]
        do Add(all, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, Int(s1^(Int(b^(-k))))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q mod 3 = 2 and q > 2 then
      for k in [0..(q - 1)/2]
        do Add(all, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, Int(s1^(Int(b^(-k))))]] ]);
      od;
    fi;

    func := function(q)
      local i, j, k, ll;
        ll := [];
        for i in [1..Int((q - 4)/3)] do
          for j in [i + 1..Int((q - 2 - i)/2)] do
            if ((q - 1 - i - j) mod (q - 1) <> i) and ((q - 1 - i - j) mod (q - 1) <> j) and (-i) mod (q - 1) <> j then
              Add(ll, [(-i) mod (q - 1), j]);
              Add(ll, [(-i) mod (q - 1), (q - 1 - i - j)]);
            fi;
          od;
        od;
      return ll;
    end;    #explength := 1/6*(q^2 - 8*q + 15 + 4*msg.w((q - 1), 3));

    if (p - 1) mod q = 0 and q > 3 then
      for k in func(q) do
        Add(all, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]] ]);
      od;
    fi;

    if (p^2 + p + 1 ) mod q = 0 and q > 3 then
      matGL3 := msg.QthRootGL3P(p, q);
      Add(all, [ [q, p, p, p],
      [2, 1, [2, Int(matGL3[1][1]), 3, Int(matGL3[2][1]), 4, Int(matGL3[3][1])]],
      [3, 1, [2, Int(matGL3[1][2]), 3, Int(matGL3[2][2]), 4, Int(matGL3[3][2])]],
      [4, 1, [2, Int(matGL3[1][3]), 3, Int(matGL3[2][3]), 4, Int(matGL3[3][3])]] ]); ## (C_q \ltimes C_p^3) when q | (p^2 + p + 1)
    fi;

    ## class 4: when P is extraspecial of type +
    if (p - 1) mod q = 0 then
      Append(all, [ [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [3, 1, [3, Int(s1)]], [2, 1, [2, Int(s1^(-1))]] ],  ## q | (p - 1), Z(G) = C_p
      [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, Int(s1)]], [2, 1, [2, Int(s1)]] ] ]);  ## q | (p - 1), Z(G) = 1
    fi;
    if (p - 1) mod q = 0 and q > 2 then
      for k in [2..(q + 1)/2] do
        Add(all, [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, Int(s1)]], [3, 1, [3, Int(s1^k)]], [2, 1, [2, Int(s1^(q + 1 - k))]] ]); ## q | (p - 1), Z(G) = 1
      od;
    fi;
    if (p + 1) mod q = 0 and q > 2 and p > 2 then
      matGL2 := msg.QthRootGL2P(p, q);;
      Add(all, [ [q, p, p, p],
      [3, 2, [3, 1, 4, 1]],
      [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]],
      [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]); ## q | (p + 1), Z(G) = C_p
    fi;

    ## class 5: when P is extraspecial of type -,
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, iii, 4, qqq]], [4, 1, [4, iii]] ]);
    fi;

    ## class 6: special cases for p = 2 and q = 3
    if p = 2 and q = 3 then
      Add(all, [ [3, 2, 2, 2], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ]);
    fi;
    list := List(all, x -> msg.groupFromData(x));
  return list;
end;
######################################################
msg.NumberGroupsP3Q := function(n)
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
          m := 5 + (5+p)*msg.w((q-1), p) + 2*msg.w((q-1), p^2)
            + msg.w((q-1), p^3) + (36+q^2+13*q+4*msg.w((q-1),3))*msg.w((p-1), q)/6
            + 2*msg.w((p+1), q) + msg.w((p^2+p+1), q)*(1 - msg.delta(q, 3));
        elif n mod 2 = 1 and q = 3 then
          m := 5 + (5+p)*msg.w((q-1), p) + 2*msg.w((q-1), p^2)
            + msg.w((q-1), p^3) + (36+q^2+13*q+4*msg.w((q-1),3))*msg.w((p-1), q)/6
            + 2*msg.w((p+1), q);
        else m := 5 + 7*msg.delta(p,2) + 2*msg.w((q-1),4) + msg.w((q-1), 8)
            + 10*msg.delta(q, 2) + 3*msg.delta(n,24) + msg.delta(n, 56); fi;
        return m;
      end;
######################################################
msg.isp3q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i->  i[2]) in [ [ 3, 1 ], [ 1, 3 ] ];
############################################################################
msg.GroupP3Q := function(n, i)
  local fac, p, q, all, G, a, b, c, d, e, f, r1, r2, r3, s1, s2, s3, s, ii, qq, iii, qqq,
  matGL2, matGL3, func, k, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
      Error("Argument must be of the form of p^3q"); fi;
    p := fac[2];
    if fac[1] = fac[2] then
    q := fac[4]; elif fac[3] = fac[4] then
    q := fac[1]; fi;
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
    ######## enumeration
    c1 := msg.delta(n, 24) + msg.w((q - 1), p) + msg.w((q - 1), p^2) + msg.w((q - 1), p^3);
    c2 := 2*msg.w((q - 1), p) + msg.w((q - 1), p^2);
    c3 := msg.w((q - 1), p);
    c4 := msg.w((q - 1), p) + msg.delta(p, 2);
    c5 := p*msg.w((q - 1), p)*(1 - msg.delta(p, 2)) + msg.delta(p, 2);
    c6 := msg.w((p - 1), q);
    c7 := (q + 1)*msg.w((p - 1), q);
    c8 := (1 - msg.delta(q, 2))*(
    1/6*(q^2 + 4*q + 9 + 4*msg.w((q - 1), 3))*msg.w((p - 1), q)
    + msg.w((p^2 + p + 1), q)*(1 - msg.delta(q, 3))
    + msg.w((p + 1), q)*(1 - msg.delta(q, 2)))
    + 3*msg.delta(q, 2);
    c9 := (1/2*(q + 3)*msg.w((p - 1), q) + msg.w((p + 1), q))*(1 - msg.delta(q, 2))*(1 - msg.delta(p, 2))
    + 2*msg.delta(q, 2);
    c10 := msg.w((p - 1), q);
############ add abelian groups in:
    all := [ [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, q], [1, [2, 1]] ], [ [p, p, p, q] ] ];
    if i < 4 then return msg.groupFromData(all[i]); fi;
############ case 1: no normal Sylow subgroup -- necessarily n = 24
    if n = 24 and i = 4 then
      return msg.groupFromData([ [2, 3, 2, 2], [2, 1, [2, 2]], [3, 1, [4, 1]], [3, 2, [4, 1]], [4, 1, [3, 1]], [4, 2, [3, 1, 4, 1]] ]);
    fi;

############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
    if i > 3 and i < 6 and p > 2 then
      Append(all, [ [ [p, p, p, q], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p, q], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ]);
      return msg.groupFromData(all[i]);
    elif i > 3 + msg.delta(n, 24) and i < 6 + msg.delta(n, 24) and p = 2 then
      Append(all, [ [ [2, 2, 2, q], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ]);
      return msg.groupFromData(all[i - msg.delta(n, 24)]);
    fi;

############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
    ## class 1: when P = C_{p^3}
    if i > 5 + msg.delta(n, 24) and i < 6 + c1 then
      l1 := [];
      if (q - 1) mod p = 0 then
        Add(l1, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_p
      fi;
      if (q - 1) mod (p^2) = 0 then
        Add(l1, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r2)]], [4, 2, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_{p^2}
      fi;
      if (q - 1) mod (p^3) = 0 then
        Add(l1, [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(r3)]], [4, 2, [4, Int(r2)]], [4, 3, [4, Int(r1)]] ]); ##C_{p^3} \ltimes_\phi C_q with \Im\phi \cong C_{p^3}
      fi;
      return msg.groupFromData(l1[i - 5 - msg.delta(n, 24)]);
    fi;
    ## class 2: when P = C_{p^2} \times C_p, there are at most two isom types of semidirect products of P \ltimes Q
    if i > 5 + c1 and i < 6 + c1 + c2 then
      l2 := [];
      if (q - 1) mod p = 0 then
        Append(l2, [ [ [p, p, p, q], [1, [2, 1]], [4, 3, [4, Int(r1)]] ], [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, Int(r1)]] ] ]);
      fi;
      if (q - 1) mod (p^2) = 0 then
        Add(l2, [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, Int(r2)]], [4, 2, [4, Int(r1)]] ]);
      fi;
      return msg.groupFromData(l2[i - 5 - c1]);
    fi;
    ## class 3: when P is elementary abelian, there is at most one isom type of P \ltimes Q
    if i > 5 + c1 + c2 and i < 6 + c1 + c2 + c3 then
      l3 := [];
      if (q - 1) mod p = 0 then
        Add(l3, [ [p, p, p, q], [4, 1, [4, Int(r1)]] ]);
      fi;
      return msg.groupFromData(l3[i - 5 - c1 - c2]);
    fi;
    ## class 4: when P is extraspecial + type, there is at most one isom type of P \ltimes Q
    if i > 5 + c1 + c2 + c3 and i < 6 + c1 + c2 + c3 + c4 then
      l4 := [];
      if (q - 1) mod p = 0 then
        Add(l4, [ [p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [4, Int(r1)]] ]);
      fi;
      if p = 2 then
        Add(l4, [ [2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q - 1]] ]);
      fi;
      return msg.groupFromData(l4[i - 5 - c1 - c2 - c3]);
    fi;
    ## class 5: when P is extraspecial - type, there is at most one isom type of P \ltimes Q
    if i > 5 + c1 + c2 + c3 + c4 and i < 6 + c1 + c2 + c3 + c4 + c5 then
      l5 := [];
      if (q - 1) mod p = 0 and p > 2 then
        for k in [1..p - 1] do
          Add(l5, [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, Int(r1^k)]] ]);
        od;
        Add(l5, [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 2, [4, Int(r1)]] ]);
      fi;
      ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
      if p = 2 and q > p then
        Add(l5, [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q - 1]] ]);
      fi;
      return msg.groupFromData(l5[i - 5 - c1 - c2 - c3 - c4]);
    fi;

############ case 4: nonabelian and only the Sylow p-subgroup is normal
    if (p - 1) mod q = 0 then
      s1 := a^((p - 1)/q);

      c := ZmodnZObj(Int(Z(p)), p^3);
      if not c^(p - 1) = ZmodnZObj(1, p^2) then
        d := c;
      else d := c + 1;
      fi;
      s3 := d^((p^3 - p^2)/q);

      s := Int(s3) mod p;
      ii := (Int(s3) - s)/p mod p;
      qq := ((Int(s3) - s)/p - ii)/p;

      e := ZmodnZObj(Int(Z(p)), p^2);
      if not e^(p - 1) = ZmodnZObj(1, p^2) then
        f := e;
      else f := e + 1;
      fi;

      s2 := f^((p^2-p)/q);
      iii := Int(s2) mod p;
      qqq := (Int(s2) - iii)/p;
    fi;

    ## class 1: when P is cyclic, there is at most isom type of semidirect products of Q \ltimes P
    if i > 5 + c1 + c2 + c3 + c4 + c5 and i < 6 + c1 + c2 + c3 + c4 + c5 + c6 then
      l6 := [];
      if (p - 1) mod q = 0 then
        Add(l6, [ [q, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, s, 3, ii, 4, qq]], [3, 1, [3, s, 4, ii]], [4, 1, [4, s]] ]);
      fi;
      return msg.groupFromData(l6[i - 5 - c1 - c2 - c3 - c4 - c5]);
    fi;
    ## class 2: when P = C_{p^2} \times C_p, there are at most (q + 1) isomorphism types of Q \ltimes P
    if i > 5 + c1 + c2 + c3 + c4 + c5 + c6 and i < 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 then
      l7 := [];
      if (p - 1) mod q = 0 then
        Append(l7, [ [ [q, p, p, p], [3, [4, 1]], [2, 1, [2, Int(s1)]] ], ## (C_q \ltimes C_p) \times C_{p^2}
        [ [q, p, p, p], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ] ]); ## (C_q \ltimes C_{p^2}) \times C_p
        for k in [1..(q - 1)] do
          Add(l7, [ [q, p, p, p], [ 2, [3, 1]], [2, 1, [2, (Int(s2) mod p), 3, ((Int(s2) - (Int(s2) mod p))/p)]], [3, 1, [3, (Int(s2) mod p)]], [4, 1, [4, Int(s1^k)]] ]); ## C_q \ltimes (C_{p^2} \times C_p)
        od;
      fi;
      return msg.groupFromData(l7[i - 5 - c1 - c2 - c3 - c4 - c5 - c6]);
    fi;
    ## class 3: when P is elementary abelian
    if i > 5 + c1 + c2 + c3 + c4 + c5 + c6 + c7 and i < 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 then
      l8 := [];
      if (p - 1) mod q = 0 then
        Add(l8, [ [q, p, p, p], [4, 1, [4, Int(s1)]] ]); ## C_q \ltimes C_p \times C_p^2
      fi;
      if (p - 1) mod q = 0 and q > 2 then
        for k in [0..(q - 1)/2] do
          Add(l8, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^k)))]] ]); ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
        od;
      fi;
      if q = 2 then
        Add(l8, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]] ]);
      fi;

      if (p + 1) mod q = 0 and q > 2 then
        matGL2 := msg.QthRootGL2P(p, q);;
        Add(l8, [ [q, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]); ## (C_q \ltimes C_p^2) \times C_p when q | (p + 1)
      fi;

      ## below: (C_q \ltimes C_p^3) when q | (p - 1)
      if q = 2 then
        Add(l8, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1)]] ]);
      fi;
      if (p - 1) mod 3 = 0 and q = 3 then
        for k in [0, 1] do
          Add(l8, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 and q > 3 then
        for k in Filtered([1..(q - 2)], x-> not x = (q - 1)/2) do
          Add(l8, [ [q, p, p ,p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1)]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 and q > 2 then
        for k in [0..(q - 1)/2]
          do Add(l8, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^k)))]], [4, 1, [4, Int(s1^(Int(b^(-k))))]] ]);
        od;
      fi;

      func := function(q)
        local i, j, k, ll;
          ll := [];
          for i in [1..Int((q - 4)/3)] do
            for j in [i + 1..Int((q - 2 - i)/2)] do
              if ((q - 1 - i - j) mod (q - 1) <> i) and ((q - 1 - i - j) mod (q - 1) <> j) and (-i) mod (q - 1) <> j then
                Add(ll, [(-i) mod (q - 1), j]);
                Add(ll, [(-i) mod (q - 1), (q - 1 - i - j)]);
              fi;
            od;
          od;
        return ll;
      end;      #explength := 1/6*(q^2 - 8*q + 15 + 4*msg.w((q - 1), 3));

      if (p - 1) mod q = 0 and q > 3 then
        for k in func(q) do
          Add(l8, [ [q, p, p, p], [2, 1, [2, Int(s1)]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]] ]);
        od;
      fi;

      if (p^2 + p + 1 ) mod q = 0 and q > 3 then
        matGL3 := msg.QthRootGL3P(p, q);
        Add(l8, [ [q, p, p, p],
        [2, 1, [2, Int(matGL3[1][1]), 3, Int(matGL3[2][1]), 4, Int(matGL3[3][1])]],
        [3, 1, [2, Int(matGL3[1][2]), 3, Int(matGL3[2][2]), 4, Int(matGL3[3][2])]],
        [4, 1, [2, Int(matGL3[1][3]), 3, Int(matGL3[2][3]), 4, Int(matGL3[3][3])]] ]); ## (C_q \ltimes C_p^3) when q | (p^2 + p + 1)
      fi;
      return msg.groupFromData(l8[i - 5 - c1 - c2 - c3 - c4 - c5 - c6 - c7]);
    fi;

    ## class 4: when P is extraspecial of type +
    if i > 5 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 and i < 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 then
      l9 := [];
      if (p - 1) mod q = 0 then
        Append(l9, [ [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [3, 1, [3, Int(s1)]], [2, 1, [2, Int(s1^(-1))]] ],  ## q | (p - 1), Z(G) = C_p
        [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, Int(s1)]], [2, 1, [2, Int(s1)]] ] ]);  ## q | (p - 1), Z(G) = 1
      fi;
      if (p - 1) mod q = 0 and q > 2 then
        for k in [2..(q + 1)/2] do
          Add(l9, [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, Int(s1)]], [3, 1, [3, Int(s1^k)]], [2, 1, [2, Int(s1^(q + 1 - k))]] ]); ## q | (p - 1), Z(G) = 1
        od;
      fi;
      if (p + 1) mod q = 0 and q > 2 and p > 2 then
        matGL2 := msg.QthRootGL2P(p, q);
        Add(l9, [ [q, p, p, p],
        [3, 2, [3, 1, 4, 1]],
        [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]],
        [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]); ## q | (p + 1), Z(G) = C_p
      fi;
      return msg.groupFromData(l9[i - 5 - c1 - c2 - c3 - c4 - c5 - c6 - c7 - c8]);
    fi;
    ## class 5: when P is extraspecial of type -
    if i > 5 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 and i < 6 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 then
      l10 := [];
      if (p - 1) mod q = 0 then
        Add(l10, [ [q, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, iii, 4, qqq]], [4, 1, [4, iii]] ]);
      fi;
      return msg.groupFromData(l10[i - 5 - c1 - c2 - c3 - c4 - c5 - c6 - c7 - c8 - c9]);
    fi;
    ## class 6: special cases for p = 2 and q = 3
    if p = 2 and q = 3 and i = 15 then
      return msg.groupFromData([ [3, 2, 2, 2], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ]);
    fi;
end;
