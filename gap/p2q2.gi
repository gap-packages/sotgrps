############################################################################ all groups P2Q2
msg.allGroupsP2Q2 := function(n)
  local fac, p, q, a, b, c, d, e, f, qq, ii, qqq, iii, all, list, k, t, matq, matq2, matp, matp2;
    fac := Factors(n);
    if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
      Error("Argument has to be of the form p^2*q^2, where p, q are primes");
    fi;
    q := fac[1];
    p := fac[4];
    #### case1: abelian, q > 2
    all := [ [ [p, p, q, q], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, q, q], [3, [4, 1]] ], [ [p, p, q, q], [1, [2, 1]] ], [ [p, p, q, q], [2, [3, 1]] ] ];

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

    #### case2: q mid (p - 1), q^2 nmid (p^2 - 1)
    if (p - 1) mod q = 0 and q > 2 or n = 36 then
      if q mod 2 = 1 then
        t := (q - 1)/2;
      else t := 0;
      fi;

      ii := Int(d^(p*(p-1)/q)) mod p;
      qq := (Int(d^(p*(p-1)/q)) - ii)/p;
      #1: P \cong C_{p^2}, Q \cong C_{q^2}
      Add(all, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);

      #2: P \cong C_{p^2}, Q \cong C_q^2
      Add(all, [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ]);

      #3: P\cong C_p^2, Q \cong C_{q^2}
      Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]] ]);
      for k in [0..t] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(Int(b^k)*(p-1)/q))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
      od;

      #4: P\cong C_p^2, Q \cong C_q^2
      Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]] ]); ##C_q \times (C_q \ltimes C_p) \times C_p, \phi(Q) = C_q
      for k in [0..t] do
        Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int((a^(Int(b^k)*(p-1)/q)))]] ]); ##C_q \times (C_q \ltimes C_p^2), \phi(Q) = C_q
      od;
      Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int(a^((p-1)/q))]] ]); ##((C_q \times C_q) \ltimes C_p) \times C_p, \phi(Q) = C_q^2
    fi;

    #### case3: q mid (p + 1), q^2 nmid (p^2 - 1)
    if (p + 1) mod q = 0 and q mod 2 = 1 then
      matq := msg.QthRootGL2P(p, q);
      #1: P \cong C_{p^2}, Q \cong C_{q^2}
      #none

      #2: P \cong C_{p^2}, Q \cong C_q^2
      #none

      #3: P \cong C_p^2, Q \cong C_{q^2}
      Add(all, [ [q, q, p, p], [1, [2, 1]],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);

      #4: P \cong C_p^2, Q \cong C_q^2
      Add(all, [ [q, q, p, p],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;
    if n = 36 then
      matq := msg.QthRootGL2P(2, 3);
      Append(all, [
      [ [3, 3, 2, 2], [1, [2, 1]], #3: P \cong C_p^2, Q \cong C_{q^2}, nontrivial centre
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ],
      [ [3, 3, 2, 2], #4: P \cong C_p^2, Q \cong C_q^2, nontrivial centre
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]
      ]);
    fi;
    #### case4: q^2 mid (p + 1)
    if ( p + 1) mod (q^2) = 0 and q > 2 or n = 36 then
      matq2 := msg.QsquaredthRootGL2P(p, q);
      matq := matq2^q;
      #3: P \cong C_p^2, Q \cong C_{q^2}, Z(G) = 1
      Add(all, [ [q, q, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
        [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
        [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;

    #### case5: q^2 mid (p - 1)
    if (p - 1) mod (q^2) = 0 and q > 2 then
      #1: P \cong C_{p^2}, Q \cong C_{q^2}, Z(G) = 1
      ii := Int(d^(p*(p-1)/(q^2))) mod p;
      qq := (Int(d^(p*(p-1)/(q^2))) - ii)/p;
      iii := Int(d^(p*(p - 1)/q)) mod p;
      qqq := (Int(d^(p*(p - 1)/q)) - iii)/p;
      Add(all, [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ]);

      #2: P \cong C_{p^2}, Q \cong C_q^2
      #already covered

      #3: P\cong C_p^2, Q \cong C_{q^2}, Z(G) = 1
      Add(all,  [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/(q^2)))]], [3, 2, [3, Int(a^((p - 1)/q))]] ]);
      for k in [0..(q^2 - q)/2] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [4, 1, [4, Int((a^(Int(f^k)*(p-1)/(q^2))))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int((a^(Int(f^k)*(p-1)/q)))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
      od;
      for k in [1..(q - 1)] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(k*(p-1)/q))]] ]);
      od;
      #4: P \cong C_p^2, Q \cong C_q^2
      #already covered
    fi;

    ####case6 q = 2 and p > 3
    if q = 2 and p > 3 then
      #1: P \cong C_{p^2}, Q \cong C_{q^2}
      Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, p - 1, 4, p - 1]], [4, 1, [4, p - 1]] ]); #Z(G) \cong C_2
      if p mod 4 = 1 then #Z(G) = 1
        ii := Int(d^((p^2-p)/4)) mod p;
        qq := (Int(d^((p^2-p)/4)) - ii)/p;
        Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, p - 1, 4, p - 1]], [4, 2, [4, p - 1]] ]);
      fi;

      #2: P \cong C_{p^2}, Q \cong C_q^2
      Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, (p - 1)]] ]);
      Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ]);

      #3: P \cong C_p^2, Q \cong C_{q^2}
      Add(all, [ [2, 2, p, p], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ]);
      if p mod 4 = 1 then
        ii := Int(d^((p^2-p)/4)) mod p;
        qq := (Int(d^((p^2-p)/4)) - ii)/p;
        Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ]);
        Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
        Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^(3*(p - 1)/4))]], [4, 2, [4, p-1]] ]);
        Add(all, [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ]);
      elif p mod 4 = 3 then
        matq2 := msg.QsquaredthRootGL2P(p, 2);
        matq := matq2^q;
        Add(all, [ [2, 2, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
        [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
        [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
      fi;
      #4: P \cong C_p^2, Q \cong C_q^2
      Add(all, [ [2, 2, p, p], [3, 1, [3, p - 1]] ]);
      Add(all, [ [2, 2, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ]);
      Add(all, [ [2, 2, p, p], [3, 1, [3, p-1]], [4, 2, [4, p-1]] ]);
    fi;
    list := List(all, x -> msg.groupFromData(x));
  return list;
end;
##
############################################################################
msg.NumberGroupsP2Q2 := function(n)
		local fac, p, q, w;
				fac := Factors(n);
				## check input
				if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
					Error("Argument has to be of the form p^2*q^2, where p, q are primes");
				fi;

				q := fac[1];
				p := fac[4];
				if n = 36 then w := 14;
				elif q = 2 then w := 11 + 5*msg.w((p-1), 4) + msg.w((p+1), 4);
				else w := 4 + (6+q)*msg.w((p-1), q) + (4+q+q^2)*msg.w((p-1), q^2)/2 + 2*msg.w((p+1),q) + msg.w((p+1), q^2);
				fi;
			return w;
		end;
############################################################################

msg.isp2q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2]) = [ 2, 2 ];

############################################################################ all groups P2Q2
msg.GroupP2Q2 := function(n, i)
  local fac, p, q, a, b, c, d, e, f, qq, ii, qqq, iii, l0, lst, G, k, t, matq, matq2, matp, matp2,
  c1, c2, c3, c4, c5;
    fac := Factors(n);
    if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
      Error("Argument has to be of the form p^2*q^2, where p, q are primes");
		fi;
    q := fac[1];
    p := fac[4];
    #### case1: q nmid (p-1), q nmid (p^2 -1), q > 2
    l0 := [ [ [p, p, q, q], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, q, q], [3, [4, 1]] ], [ [p, p, q, q], [1, [2, 1]] ], [ [p, p, q, q], [2, [3, 1]] ] ];
    if i < 5 then return msg.groupFromData(l0[i]); fi;
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
    #### Enumeration
    c1 := msg.w((p - 1), q)*(q + 6)*(1 - msg.delta(q, 2)) + 7*msg.delta(n, 36);
    c2 := 2*msg.w((p + 1), q)*(1 - msg.delta(q, 2)) + 2*msg.delta(n, 36);
    c3 := msg.w((p + 1), q^2)*(1 - msg.delta(q, 2)) + msg.delta(n, 36);
    c4 := msg.w((p - 1), q^2)*((q^2 + q + 4)/2)*(1 - msg.delta(q, 2));
    c5 := msg.delta(q, 2)*(7*(1 - msg.delta(p, 3)) + 5*msg.w((p - 1), 4) + msg.w((p + 1), 4));
    #### case2: q mid (p - 1), q^2 nmid (p^2 - 1)
    if i > 4 and i < 5 + c1 then
      if ((p - 1) mod q = 0 and q > 2 or n = 36) then
        lst := [];
        ii := Int(d^(p*(p-1)/q)) mod p;
        qq := (Int(d^(p*(p-1)/q)) - ii)/p;
        Append(lst, [ [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ], ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
        [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ], ##C_q^2 \ltimes C_{p^2}, \phi(Q) = C_q
        [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]] ] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
        if q mod 2 = 1 then
          t := (q - 1)/2;
        else t := 0;
        fi;
        for k in [0..t] do
          Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(Int(b^k)*(p-1)/q))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
        od;
        Add(lst, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]] ]); ##C_q \times (C_q \ltimes C_p) \times C_p, \phi(Q) = C_q
        for k in [0..t] do
          Add(lst, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int((a^(Int(b^k)*(p-1)/q)))]] ]); ##C_q \times (C_q \ltimes C_p^2), \phi(Q) = C_q
        od;
        Add(lst, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int(a^((p-1)/q))]] ]); ##((C_q \times C_q) \ltimes C_p) \times C_p, \phi(Q) = C_q^2
        return msg.groupFromData(lst[i - 4]);
      fi;
    fi;

    #### case3: q mid (p + 1), q^2 nmid (p^2 - 1)
    if i > 4 + c1 and i < 5 + c1 + c2 and (p + 1) mod q = 0 and q mod 2 = 1 then
      lst := [];
      matq := msg.QthRootGL2P(p, q);
      Append(lst, [ [ [q, q, p, p], [1, [2, 1]], ##C_{q^2} \ltimes C_p^2
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ],
      [ [q, q, p, p], ##C_q \times (C_q \ltimes C_p^2)
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] ]);
      return msg.groupFromData(lst[i - 4 - c1]);
    fi;
    if i > 4 + c1 and i < 5 + c1 + c2 and n = 36 then
      lst := [];
      matq := msg.QthRootGL2P(2, 3);
      Append(lst, [ [ [3, 3, 2, 2], [1, [2, 1]], ##C_4 \ltimes C_3^2
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ],
      [ [3, 3, 2, 2], ##C_2 \times (C_2 \ltimes C_3^2)
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] ]);
      return msg.groupFromData(lst[i - 4 - c1]);
    fi;
    #### case4: q^2 mid (p + 1)
    if (i > 4 + c1 + c2 and i < 5 + c1 + c2 + c3) then
      if (p + 1) mod (q^2) = 0 and q > 2 or n = 36 then
        lst := [];
        matq2 := msg.QsquaredthRootGL2P(p, q);
        matq := matq2^q;
        Add(lst, [ [q, q, p, p], [1, [2, 1]],
  				[3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
  				[4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
  				[3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
  				[4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
          return msg.groupFromData(lst[i - 4 - c1 - c2]);
  		fi;
    fi;

    #### case5: q^2 mid (p - 1)
    if i > 4 + c1 + c2 + c3 and i < 5 + c1 + c2 + c3 + c4 and (p - 1) mod (q^2) = 0 and q > 2 then
      lst := [];
      ii := Int(d^(p*(p-1)/(q^2))) mod p;
      qq := (Int(d^(p*(p-1)/(q^2))) - ii)/p;
      iii := Int(d^(p*(p - 1)/q)) mod p;
      qqq := (Int(d^(p*(p - 1)/q)) - iii)/p;
      Append(lst, [ [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ],  ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_{q^2}
      [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/(q^2)))]], [3, 2, [3, Int(a^((p - 1)/q))]] ] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
      for k in [0..(q^2 - q)/2] do
        Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [4, 1, [4, Int((a^(Int(f^k)*(p-1)/(q^2))))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int((a^(Int(f^k)*(p-1)/q)))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
      od;
      for k in [1..(q - 1)] do
        Add(lst, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(k*(p-1)/q))]] ]);
      od;
      return msg.groupFromData(lst[i - 4 - c1 - c2 - c3]);
    fi;

    ####case6 q = 2 and p > 3
    if i > 4 + c1 + c2 + c3 + c4 and i < 5 + c1 + c2 + c3 + c4 + c5 and q = 2 and p > 3 then
      lst := [];
      Append(lst, [ [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ], ##C_4 \ltimes C_{p^2}, \phi(Q) = C_2
      [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, (p - 1)]] ], ##C_4 \ltimes C_p^2 \phi(Q) = C_2
      [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, p-1]] ],
      [ [2, 2, p, p], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ], ##C_2^2 \ltimes C_{p^2}, \phi(Q) = C_2
      [ [2, 2, p, p], [3, 1, [3, p - 1]] ], ##C_2^2 \ltimes C_p^2, \phi(Q) = C_2
      [ [2, 2, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ],
      [ [2, 2, p, p], [3, 1, [3, p-1]], [4, 2, [4, p-1]] ] ]); ##C_2^2 \ltimes C_p^2 \phi(Q) = C_2^2
      if p mod 4 = 1 then
        ii := Int(d^((p^2-p)/4)) mod p;
        qq := (Int(d^((p^2-p)/4)) - ii)/p;
        Append(lst, [ [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, p - 1, 4, p - 1]], [4, 2, [4, p - 1]] ],  ##C_4 \ltimes C_{p^2}, \phi(Q) = C_4
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ], ##C_4 \ltimes C_p^2 \phi(Q) = C_4
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ],
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^(3*(p - 1)/4))]], [4, 2, [4, p-1]] ],
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p - 1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p - 1]] ] ]);
      fi;
      if p mod 4 = 3 then
        matq2 := msg.QsquaredthRootGL2P(p, 2);
        matq := matq2^q;
        Add(lst, [ [2, 2, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
        [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
        [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
      fi;
      return msg.groupFromData(lst[i - 4 - c1 - c2 - c3 - c4]);
    fi;

end;
