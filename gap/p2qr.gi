msg.allGroupsP2QR := function(n)
  local fac, primefac, p, q, r, coll, case1, case2, case3, case4, case5, case6, case7, case8, all;
    all := [];
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
############ add abelian groups in:
    Append(all, [AbelianGroup([n]), AbelianGroup([p*q*r, p])]);
############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
    case1 := function(p, q, r)
      local a, b, c, d, data;
        a := Z(r);
        b := a^((r-1)/(p^2*q));
        c := b^p;
        d := c^p;
        data := [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(b)]], [4, 2, [4, Int(c)]], [4, 3, [4, Int(d)]] ];
      return msg.groupFromData(data);
    end;

    if (r - 1) mod (p^2*q) = 0 then Add(all, case1(p, q, r)); fi;
############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or p | (q - 1)(r - 1)
    case2 := function(p, q, r)
      local  list, G1, G2, G3, G4, G5, G6, i;
        list := [];
        ##
        G1 := function(p, q, r) ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          local a, s, data;
            a := Z(q);
            s := a^((q-1)/(p^2));
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(s)]], [3, 2, [3, Int(s^p)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (q - 1) mod (p^2) = 0 then Add( list, G1(p, q, r)); fi;
        ##
        G2 := function(p, q, r, k) ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
          local a, b, s, t, data;
            a := Z(q);
            b := Z(r);
            s := a^((q-1)/(p^2));
            t := b^(k*(r-1)/p);
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(s)]], [3, 2, [3, Int(s^p)]], [4, 1, [4, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then
          for i in [1..p-1] do Add( list, G2(p, q, r, i));
          od;
        fi;
        ##
        G3 := function(p, q, r, k) ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
          local a, b, s, t, data;
            a := Z(q);
            b := Z(r);
            s := a^((q-1)/(p^2));
            t := b^(k*(r-1)/(p^2));
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(s)]], [3, 2, [3, Int(s^p)]], [4, 1, [4, Int(t)]], [4, 2, [4, Int(t^p)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then
          for i in msg.groupofunitsP2(p) do Add( list, G3(p, q, r, i));
          od;
        fi;
        ##
        G4 := function(p, q, r) ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
          local b, t, data;
            b := Z(r);
            t := b^((r-1)/(p^2));
            data := [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Int(t)]], [4, 2, [4, Int(t^p)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod (p^2) = 0 then
          Add( list, G4(p, q, r));
        fi;
        ##
        G5 := function(p, q, r, k) ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
          local a, b, s, t, data;
            a := Z(q);
            b := Z(r);
            s := a^(k*(q-1)/p);
            t := b^((r-1)/(p^2));
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(s)]], [4, 1, [4, Int(t)]], [4, 2, [4, Int(t^p)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then
          for i in [1..p-1]
            do Add( list, G5(p, q, r, i));
          od;
        fi;
        ##
        G6 := function(p, q, r) ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
          local a, b, s, t, data;
            a := Z(q);
            b := Z(r);
            s := a^((q-1)/p);
            t := b^((r-1)/p);
            data := [ [p, p, q, r], [3, 1, [3, Int(s)]], [4, 2, [4, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (q - 1) mod p = 0 then
          Add( list, G6(p, q, r));
        fi;
      ##
      return  list;
    end;
############
    Append(all, case2(p, q, r));
############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    case3 := function(p, q, r)
      local  list, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, i, j;
        list := [];
        G1 := function(p, q, r) ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
          local a, b, s, t, ii, qq, iii, qqq, data;
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
            s := Int(b^((p^2-p)/q));
            t := Int(b^((p^2-p)/r));
            ii := s mod p;
            qq := (s - ii)/p;
            iii := t mod p;
            qqq := (t - iii)/p;
            data := [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 and (p - 1) mod r = 0
          then Add( list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
          local a, s, t, data;
            a := Z(p);
            s := a^((p-1)/q);
            t := a^((p-1)/r);
            data := [ [q, r, p, p], [3, 1, [3, Int(s)]], [4, 2, [4, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 and (p - 1) mod r = 0
          then Add( list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r) ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
          local a, s, t, data;
            a := Z(p);
            s := a^((p-1)/q);
            t := a^((p-1)/r);
            data := [ [q, r, p, p], [3, 1, [3, Int(s)]], [3, 2, [3, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 and (p - 1) mod r = 0
          then Add( list, G3(p, q, r));
        fi;
        ##
        G4 := function(p, q, r, k) ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
          local a, s, t, data;
            a := Z(p);
            s := a^((p-1)/q);
            t := a^((p-1)/r);
            data := [ [q, r, p, p], [3, 1, [3, Int(s)]], [3, 2, [3, Int(t)]], [4, 1, [4, Int(s^i)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p-1) mod (q*r) = 0 then
          for i in [1..q-1] do
            Add( list, G4(p, q, r, i));
          od;
        fi;
        ##
        G5 := function(p, q, r, k) ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
          local a, s, t, data;
            a := Z(p);
            s := a^((p-1)/q);
            t := a^((p-1)/r);
            data := [ [q, r, p, p], [3, 1, [3, Int(s)]], [3, 2, [3, Int(t)]], [4, 2, [4, Int(t^i)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p-1) mod (q*r) = 0 then
          for i in [1..r-1] do
            Add( list, G5(p, q, r, i));
          od;
        fi;
        ##
        G6 := function(p, q, r, k, l) ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
          local a, s, t, x, y, alpha, beta, data;
            a := Z(p);
            alpha := Z(q);
            beta := Z(r);
            s := a^((p-1)/q);
            t := a^((p-1)/r);
            x := Int(alpha^k);
            y := Int(beta^l);
            data := [ [q, r, p, p], [3, 1, [3, Int(s)]], [3, 2, [3, Int(t)]], [4, 1, [4, Int(s^x)]], [4, 2, [4, Int(t^y)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p-1) mod (q*r) = 0 and q > 2 then
          for i in [0..(q-1)/2] do
            for j in [0..(r-1)/2] do
              Add( list, G6(p, q, r, i, j));
            od;
          od;
        fi;
        ##
        ##
        if (p-1) mod (q*r) =0 and q > 2 then
          for i in [1..(q-3)/2] do
            for j in [(r+1)/2..(r-1)] do
              Add( list, G6(p, q, r, i, j));
            od;
          od;
        fi;
        ##
        ##
        if (p-1) mod (q*r) = 0 and q = 2 then
          for j in [0..(r-1)/2] do
            Add( list, G6(p, q, r, 0, j));
          od;
        fi;
        ##
        G7 := function(p, q, r) ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
          local a, t, data;
            a := Z(p);
            t := a^((p-1)/r);
            data := [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Int(t)]], [4, 1, [3, 1]], [4, 2, [4, Int(t^(-1))]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p-1) mod (q*r) = 0 and q = 2 then
          Add( list, G7(p, q, r));
        fi;
        ##
        G8 := function(p, q, r) ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
          local matqr, matr, data;
            matqr := msg.QthRootGL2P(p, (q*r));
            matr := matqr^q;
            data := [ [q, r, p, p], [1, [2, 1]],
            [3, 1, [3, Int(matqr[1][1]), 4, Int(matqr[2][1])]],
            [4, 1, [3, Int(matqr[1][2]), 4, Int(matqr[2][2])]],
            [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
            [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p+1) mod (q*r) = 0 and q > 2 then
          Add( list, G8(p, q, r));
        fi;
        ##
        G9 := function(p, q, r) ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
          local matq, matr, data;
            matr := msg.QthRootGL2P(p, r);
            data := [ [q, r, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]],
            [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
            [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p+1) mod (q*r) = 0 and q = 2 then
          Add( list, G9(p, q, r));
        fi;
        ##
        G10 := function(p, q, r) ## qr | (p + 1), q = 2, and G \cong (C_q \ltimes C_r)\ltimes C_p^2
          local matq, matr, data;
            matr := msg.QthRootGL2P(p, r);
            data := [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [4, 1, [3, 1]],
            [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
            [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p+1) mod (q*r) = 0 and q = 2 then
          Add( list, G10(p, q, r));
        fi;
        ##
        G11 := function(p, q, r) ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
          local a, t, matr, data;
            a := Z(p);
            t := a^((p - 1)/q);
            matr := msg.QthRootGL2P(p, r);
            data := [ [q, r, p, p], [3, 1, [3, Int(t)]], [4, 1, [4, Int(t)]],
            [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
            [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then
          Add( list, G11(p, q, r));
        fi;
        ##
        G12 := function(p, q, r) ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
          local a, s, matq, data;
            a := Z(p);
            s := a^((p - 1)/r);
            matq := msg.QthRootGL2P(p, q);
            data := [ [q, r, p, p],
            [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
            [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
            [3, 2, [3, Int(s)]], [4, 2, [4, Int(s)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then
          Add( list, G12(p, q, r));
        fi;
        ##
      return list;
    end;
############
    Append(all, case3(p, q, r));
############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    case4 := function(p, q, r)
      local list, G1, G2, G3, G4, i;
        list := [];
        G1 := function(p, q, r) ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
          local a, b, ii, qq, s, data;
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
            s := Int(b^((p^2-p)/r));
            ii := s mod p;
            qq := (s - ii)/p;
            data := [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod r = 0 then
          Add(list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
          local a, s, data;
            a := Z(p);
            s := Int(a^((p-1)/r));
            data := [ [r, p, p, q], [2, 1, [2, s]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod r = 0 then
          Add(list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r, k) ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          local a, b, c, s, t, data;
            a := Z(p);
            b := Z(r);
            c := Int(b^k);
            s := Int(a^((p-1)/r));
            t := Int(a^(c*(p-1)/r));
            data := [ [r, p, p, q], [2, 1, [2, s]], [3, 1, [3, t]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod r = 0 and r > 2 then
          for i in [0..(r - 1)/2] do
           Add(list, G3(p, q, r, i));
          od;
        fi;
        ##
        if r = 2 then Error("r must be a prime greater than q");
        fi;
        ##
        G4 := function(p, q, r) ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
          local matr, data;
            matr := msg.QthRootGL2P(p, r);
            data := [ [r, p, p, q],
            [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
            [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p + 1) mod r = 0 and r > 2 then
          Add(list, G4(p, q, r));
        fi;
        ##
        if r = 2 then Error("r must be a prime greater than q");
        fi;
        ##
      return list;
    end;
############
    Append(all, case4(p, q, r));
############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    case5 := function(p, q, r)
      local list, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, i, j;
        list := [];
        G1 := function(p, q, r) ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
          local a, b, data;
            a := Z(r);
            b := a^((r-1)/q);
            data := [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod q = 0 then
          Add(list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
          local a, b, ii, qq, s, data;
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
            s := Int(b^((p^2-p)/q));
            ii := s mod p;
            qq := (s - ii)/p;
            data := [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 then
          Add(list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r, k) ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
          local a, b, c, ii, qq, s, t, data;
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
            s := Int(b^((p^2-p)/q));
            ii := s mod p;
            qq := (s - ii)/p;
            c := Z(r);
            t := c^(k*(r-1)/q);
            data := [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 and (r - 1) mod q = 0 then
          for i in [1..(q-1)] do
            Add(list, G3(p, q, r, i));
          od;
        fi;
        ##
        G4 := function(p, q, r) ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
          local a, s, data;
            a := Z(p);
            s := Int(a^((p-1)/q));
            data := [ [q, p, p, r], [2, 1, [2, s]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 then
          Add(list, G4(p, q, r));
        fi;
        ##
        G5 := function(p, q, r, k) ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
          local a, b, c, s, t, data;
            a := Z(p);
            b := Z(q);
            c := Int(b^k);
            s := Int(a^((p-1)/q));
            t := Int(a^(c*(p-1)/q));
            data := [ [q, p, p, r], [2, 1, [2, s]], [3, 1, [3, t]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p - 1) mod q = 0 and q > 2 then
          for i in [0..(q - 1)/2] do
           Add(list, G5(p, q, r, i));
          od;
        fi;
        ##
        if (p - 1) mod q = 0 and q = 2 then
          Add(list, G5(p, q, r, 0));
        fi;
        ##
        G6 := function(p, q, r) ## q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          local mat, data;
            mat := msg.QthRootGL2P(p, q);
            data := [ [q, r, p, p], [3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]], [4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p + 1) mod q = 0 and q > 2 then
          Add(list, G6(p, q, r));
        fi;
        ##
        G7 := function(p, q, r) ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
          local a, b, data;
            a := Z(r);
            b := a^((r - 1)/q);
            data := [ [q, r, p, p], [2, 1, [2, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod q = 0 then
          Add(list, G7(p, q, r));
        fi;
        ##
        G8 := function(p, q, r, l) ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          local a, b, s, t, data;
            a := Z(r);
            b := Z(p);
            s := a^((r-1)/q);
            t := b^((p-1)/q);
            data := [ [q, r, p, p], [2, 1, [2, Int(s^l)]], [3, 1, [3, Int(t)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod q = 0 and (p - 1) mod q = 0 then
          for i in [1..q-1] do
            Add(list, G8(p, q, r, i));
          od;
        fi;
        ##
        G9 := function(p, q, r, l, k) ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          local a, b, c, d, e, s, t, data;
            a := Z(r);
            b := Z(p);
            c := Z(q);
            d := Int(c^l);
            e := Int(c^k);
            s := a^((r-1)/q);
            t := b^((p-1)/q);
            data := [ [q, r, p, p], [2, 1, [2, Int(s^d)]], [3, 1, [3, Int(t)]], [4, 1, [4, Int(t^e)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
          for j in [0..(q - 3)/2] do
            Add(list, G9(p, q, r, 0, j));
          od;
        fi;

        if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
          for i in [1..(q - 3)/2] do
            for j in [0..(q - 1)/2] do
                Add(list, G9(p, q, r, i, j));
            od;
          od;
        fi;

        if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
          Add(list, G9(p, q, r, (q - 1)/2, (q - 1)/2));
        fi;

        if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
          for i in [(q - 1)/2..q - 2] do
            for j in [0..(q - 3)/2] do
              Add(list, G9(p, q, r, i, j));
            od;
          od;
        fi;
        ##
        if q = 2 then
          Add(list, G9(p, q, r, 1, 0));
        fi;
        ##
        G10 := function(p, q, r, k) ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
          local matq, a, b, c, data;
            matq := msg.QthRootGL2P(p, q);
            a := Z(r);
            b := matq^k;
            c := a^((r - 1)/q);
            data := [ [q, r, p, p], [2, 1, [2, Int(c)]], [3, 1, [3, Int(b[1][1]), 4, Int(b[2][1])]], [4, 1, [3, Int(b[1][2]), 4, Int(b[2][2])]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then
          for i in [1..(q-1)/2] do
            Add(list, G10(p, q, r, i));
          od;
        fi;
        ##
      return list;
    end;
############
    Append(all, case5(p, q, r));
############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    case6 := function(p, q, r)
      local list, G1, G2, G3, G4, i, j;
        list := [];
        G1 := function(p, q, r) ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
          local a, b, c, data;
            a := Z(r);
            b := a^((r-1)/p);
            c := a^((r-1)/q);
            data := [ [p, q, p, r], [4, 1, [4, Int(b)]], [4, 2, [4, Int(c)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (r - 1) mod q = 0 then
          Add(list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
          local a, b, c, data;
            a := Z(r);
            b := a^((r-1)/p);
            c := a^((r-1)/q);
            data := [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Int(b)]], [4, 2, [4, Int(c)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (r - 1) mod q = 0 then
          Add(list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r) ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
          local a, b, c, d, data;
            a := Z(r);
            b := Z(p);
            c := a^((r-1)/p);
            d := b^((p-1)/q);
            data := [ [p, r, q, p], [2, 1, [2, Int(c)]], [4, 3, [4, Int(d)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (p - 1) mod q = 0 then
          Add(list, G3(p, q, r));
        fi;
        ##
        G4 := function(p, q, r, k) ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
          local a, b, c, d, e, data;
            a := Z(r);
            b := Z(p);
            c := a^((r-1)/p);
            d := a^((r-1)/q);
            e := b^((p-1)/q);
            data := [ [p, q, r, p], [3, 1, [3, Int(c)]], [3, 2, [3, Int(d)]], [4, 2, [4, Int(e^k)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then
          for i in [1..q-1] do
            Add(list, G4(p, q, r, i));
          od;
        fi;
          ##
      return list;
    end;
############
    Append(all, case6(p, q, r));
############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    case7 := function(p, q, r)
      local list, G1, G2, G3, i, j;
        list := [];
        G1 := function(p, q, r) ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
          local a, b, data;
            a := Z(r);
            b := a^((r-1)/p);
            data := [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 then
          Add(list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
          local a, b, data;
            a := Z(q);
            b := a^((q-1)/p);
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (q - 1) mod p = 0 then
          Add(list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r, k) ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
          local a, b, c, d, data;
            a := Z(q);
            b := Z(r);
            c := a^((q-1)/p);
            d := b^(k*(r-1)/p);
            data := [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c)]], [4, 1, [4, Int(d)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (q - 1) mod p = 0 then
          for i in [1..p-1] do
            Add(list, G3(p, q, r, i));
          od;
        fi;
        ##
      return list;
    end;
############
    Append(all, case7(p, q, r));
############  case 8: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    case8 := function(p, q, r)
      local list, G1, G2, G3, i, j;
        list := [];
        G1 := function(p, q, r) ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
          local a, b, data;
            a := Z(r);
            b := a^((r-1)/p);
            data := [ [p, p, q, r], [4, 1, [4, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 then
          Add(list, G1(p, q, r));
        fi;
        ##
        G2 := function(p, q, r) ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
          local a, b, data;
            a := Z(q);
            b := a^((q-1)/p);
            data := [ [p, p, q, r], [3, 1, [3, Int(b)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (q - 1) mod p = 0 then
          Add(list, G2(p, q, r));
        fi;
        ##
        G3 := function(p, q, r, k) ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
          local a, b, c, d, data;
            a := Z(q);
            b := Z(r);
            c := a^((q-1)/p);
            d := b^(k*(r-1)/p);
            data := [ [p, p, q, r], [3, 1, [3, Int(c)]], [4, 1, [4, Int(d)]] ];
          return msg.groupFromData(data);
        end;
        ##
        if (r - 1) mod p = 0 and (q - 1) mod p = 0 then
          for i in [1..p-1] do
            Add(list, G3(p, q, r, i));
          od;
        fi;
      ##
      return list;
    end;
############
    Append(all, case8(p, q, r));
############
    if n = 60 then
      Add(all, AlternatingGroup(5));
    fi;
############
  return all;
end;

######################################################
msg.NumberGroupsP2QR := function(n)
  local s, fac, primefac, p, q, r, m;
    s := [];
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

    if n = 60 then m := 13;
    fi;
    if q = 2 then
      m := 10 + (2*r + 7)*msg.deltaDivisibility((p - 1), r) + 3*msg.deltaDivisibility((p + 1), r) + 6*msg.deltaDivisibility((r - 1), p) + 2*msg.deltaDivisibility((r - 1), (p^2));
    fi;
    if q > 2 and not n = 60 then
      m := 2 + (p^2 - p)*msg.deltaDivisibility((q - 1), (p^2))*msg.deltaDivisibility((r - 1), (p^2))
      + (p - 1)*(msg.deltaDivisibility((q - 1), (p^2))*msg.deltaDivisibility((r - 1), p) + msg.deltaDivisibility((r - 1), (p^2))*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p))
      + (q - 1)*(q + 4)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)/2
      + (q - 1)*(msg.deltaDivisibility((p + 1), q)*msg.deltaDivisibility((r - 1), q) + msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p - 1), (q*r)) + 2*msg.deltaDivisibility((r - 1), (p*q))*msg.deltaDivisibility((p - 1), q))/2
      + (q*r + 1)*msg.deltaDivisibility((p - 1), (q*r))/2
      + (r + 5)*msg.deltaDivisibility((p - 1), r)*(1 + msg.deltaDivisibility((p - 1), q))/2
      + msg.deltaDivisibility((p^2 - 1), (q*r)) + 2*msg.deltaDivisibility((r - 1), (p*q)) + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((r - 1), (p^2*q))
      + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p) + 3*msg.deltaDivisibility((p - 1), q) + 2*msg.deltaDivisibility((r - 1), p)
      + 2*msg.deltaDivisibility((r - 1), q) + msg.deltaDivisibility((r - 1), (p^2)) + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((p + 1), r) + msg.deltaDivisibility((p + 1), q);
    fi;
    return m;
  end;
######################################################
msg.GroupP2QR := function(n, i)
  local fac, primefac, p, q, r, a, b, c, u, v, ii, qq, iii, qqq, k, l, matq, matr, matqr, mat, mat_k, all, G;
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
    a := Z(r);
    b := Z(p);
    c := Z(q);

    u := ZmodnZObj(Int(Z(p)), p^2);
    if not u^(p-1) = ZmodnZObj(1, p^2) then v := u;
    else v := u + 1;
    fi;
    if (p - 1) mod q = 0 then
      ii := Int(v^((p^2-p)/q)) mod p;
      qq := (Int(v^((p^2-p)/q)) - ii)/p;
    fi;
    if (p - 1) mod r = 0 then
      iii := Int(v^((p^2-p)/r)) mod p;
      qqq := (Int(v^((p^2-p)/r)) - iii)/p;
    fi;

    if (p + 1) mod (q * r) = 0 and q > 2 then
      matqr := msg.QthRootGL2P(p, (q*r));
      mat := matqr^q;
    fi;
    if (p + 1) mod r = 0 and r > 2 then
      matr := msg.QthRootGL2P(p, r);
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      matq := msg.QthRootGL2P(p, q);
    fi;
############ add abelian groups in:
    all := [ [ [p, p, q, r], [1, [2, 1]] ], [ [p, p, q, r] ] ];
############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
    if (r - 1) mod (p^2*q) = 0 then ##C_{p^2q} \ltimes C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(a^((r-1)/(p^2*q)))]], [4, 2, [4, Int(a^((r-1)/(p*q)))]], [4, 3, [4, Int(a^((r-1)/q))]] ]);
    fi;

############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or p | (q - 1)(r - 1)
    if (q - 1) mod (p^2) = 0 then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in msg.groupofunitsP2(p) do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/(p^2)))]], [4, 2, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;
    if (r - 1) mod (p^2) = 0 then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Int(a^((r-1)/(p^2)))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
    fi;
    if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1]
        do Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^(k*(q-1)/p))]], [4, 1, [4, Int(a^((r-1)/(p^2)))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
      od;
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
      Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
    fi;

############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    if (p - 1) mod q = 0 and (p - 1) mod r = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ]);
    fi;
    if (p - 1) mod q = 0 and (p - 1) mod r = 0 then ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^((p-1)/r))]] ]);
    fi;
    if (p - 1) mod q = 0 and (p - 1) mod r = 0 then ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]] ]);
    fi;
    if (p-1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(q - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(k*(p-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 then  ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(r - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 2, [4, Int(b^(k*(p-1)/r))]] ]);
      od;
    fi;
    if (p-1) mod (q*r) = 0 and q > 2 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [0..(q - 1)/2] do
        for l in [0..(r - 1)/2] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p-1) mod (q*r) =0 and q > 2 then
      for k in [1..(q-3)/2] do
        for l in [(r+1)/2..(r-1)] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then
      for l in [0..(r-1)/2] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [3, 1]], [4, 2, [4, Int(b^((1 - p)/r))]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q > 2 then ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
      Add(all, [ [q, r, p, p], [1, [2, 1]],
      [3, 1, [3, Int(matqr[1][1]), 4, Int(matqr[2][1])]],
      [4, 1, [3, Int(matqr[1][2]), 4, Int(matqr[2][2])]],
      [3, 2, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
      [4, 2, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
      Add(all, [ [q, r, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong (C_q \ltimes C_r)\ltimes C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [4, 1, [3, 1]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p - 1)/q))]], [4, 1, [4, Int(b^((p - 1)/q))]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
      [3, 2, [3, Int(b^((p - 1)/r))]], [4, 2, [4, Int(b^((p - 1)/r))]] ]);
    fi;

############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
      Add(all, [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ]);
    fi;
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
      Add(all, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]] ]);
    fi;
    if (p - 1) mod r = 0 and r > 2 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      for k in [0..(r - 1)/2] do
       Add(all, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]], [3, 1, [3, Int(b^(Int(a^k)*(p-1)/r))]] ]);
      od;
    fi;
    if (p + 1) mod r = 0 and r > 2 then ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      Add(all, [ [r, p, p, q],
      [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
      [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ]);
    fi;

############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    if (r - 1) mod q = 0 then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Int(a^((r-1)/q))]] ]);
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
      Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
    fi;
    if (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
      for k in [1..(q-1)] do
        Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(a^(k*(r-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
      Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]] ]);
    fi;
    if (p - 1) mod q = 0 and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
      for k in [0..(q - 1)/2] do
       Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int(c^k)*(p-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q = 2 then
      Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int((p-1)/q)))]] ]);
    fi;
    if (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]], [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;
    if (r - 1) mod q = 0 then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [1..q-1] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(k*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [0..(q - 3)/2] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [1..(q - 3)/2] do
        for k in [0..(q - 1)/2] do
            Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^((q - 1)/2))*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^((q - 1)/2))*(p-1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [(q - 1)/2..q - 2] do
        for k in [0..(q - 3)/2] do
          Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      od;
    fi;
    if q = 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^((p-1)/q))]] ]);
    fi;
    if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [1..(q-1)/2] do
        mat_k := matq^k;
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]], [3, 1, [3, Int(mat_k[1][1]), 4, Int(mat_k[2][1])]], [4, 1, [3, Int(mat_k[1][2]), 4, Int(mat_k[2][2])]] ]);
      od;
    fi;

############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
      Add(all, [ [p, r, q, p], [2, 1, [2, Int(a^((r-1)/p))]], [4, 3, [4, Int(b^((p-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
      for k in [1..q-1] do
        Add(all, [ [p, q, r, p], [3, 1, [3, Int(a^((r-1)/p))]], [3, 2, [3, Int(a^((r-1)/q))]], [4, 2, [4, Int(b^(k*(p-1)/q))]] ]);
      od;
    fi;

############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if (r - 1) mod p = 0 then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Int(a^((r-1)/p))]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;

############  case 8: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if (r - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [4, 1, [4, Int(a^((r-1)/p))]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;

############
    if n = 60 then
      Add(all, AlternatingGroup(5));
    fi;
############
    if not n = 60 and i < (msg.NumberGroupsP2QR(n) + 1) then
      G := msg.groupFromData(all[i]);
    elif n = 60 and i < msg.NumberGroupsP2QR(n) then
      G := msg.groupFromData(all[i]);
    elif n = 60 and i = msg.NumberGroupsP2QR(n) then
      G := AlternatingGroup(5);
    fi;
  return G;
end;
