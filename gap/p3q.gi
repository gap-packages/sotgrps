############################################################################
msg.allGroupsP3Q := function(n)
  local fac, p, q, case1, case2, case3, case4, s;
    s := [];
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 2 or not fac[2] = fac[3] then
      Error("Argument must be of the form of p^3q"); fi;
    p := fac[2];
    if fac[1] = fac[2] then
    q := fac[4]; elif fac[3] = fac[4] then
    q := fac[1]; fi;

############ add abelian groups in:
    Append(s, [AbelianGroup([n]), AbelianGroup([p^2, p*q]), AbelianGroup([p, p, p*q])]);
############ case 1: no normal Sylow subgroup -- necessarily n = 24
    if n = 24 then Add(s, PcpGroupToPcGroup(Image(IsomorphismPcpGroup(SymmetricGroup(4))))); fi;
############ case 2: nonabelian and every Sylow subgroup is normal, namely, P \times Q -- determined by the isomorphism type of P
    case2 := function(p, q)
      local data1, data2, data3, data4, l;
        l := [];
        data1 := [ [p, p, p, q], [2, 1, [2, 1, 3, 1]] ];
        data2 := [ [p, p, p, q], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
        data3 := [ [2, 2, 2, q], [2, 1, [2, 1, 3, 1]] ];
        data4 := [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
        if p > 2 then Append(l, [msg.groupFromData(data1), msg.groupFromData(data2)]);
        else Append(l, [msg.groupFromData(data3), msg.groupFromData(data4)]); fi;
      return l;
    end;
############ case 2 always exists
    Append(s, case2(p, q));
############ case 3: nonabelian and only Sylow q-subgroup is normal, namely, P \ltimes Q
    case3 := function(p, q)
      local class1, class2, class3, class4, class5, class6, l; ## classes depending on the isom type of P
        l := [];
        ## class 1: when P is cyclic, there are three isom types of semidirect products of P \ltimes Q
        class1 := function(p, q)
            local list, G1, G2, G3;
              list := [];
              G1 := function(p, q) ## G1 exists only when p divides (q - 1)
                local data;
                  data := [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int((Z(q))^((q-1)/p))]]];
                return msg.groupFromData(data);
              end;
              ##
              if (q - 1) mod p = 0 then Add(list, G1(p, q)); fi;
              ##
              G2 := function(p, q) ## G2 exists only when p^2 divides (q - 1)
                local c, r1, r2, data;
                  c := Z(q);
                  r1 := Int(c^((q-1)/p));
                  r2 := Int(c^((q-1)/(p^2)));
                  data := [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, r2]], [4, 2, [4, r1]] ];
                return msg.groupFromData(data);
              end;
              ##
              if (q - 1) mod (p^2) = 0 then Add(list, G2(p, q)); fi;
              ##
              G3 := function(p, q) ## G3 exists only when p^3 divides (q - 1)
                local c, r1, r2, r3, data;
                  c := Z(q);
                  r1 := Int(c^((q-1)/p));
                  r2 := Int(c^((q-1)/(p^2)));
                  r3 := Int(c^((q-1)/(p^3)));
                  data := [ [p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, r3]], [4, 2, [4, r2]], [4, 3, [4, r1]] ];
                return msg.groupFromData(data);
              end;
              ##
              if (q - 1) mod (p^3) = 0 then Add(list, G3(p, q)); fi;
            return list;
          end;
          ##
          Append(l, class1(p, q));
          ## class 2: when P = C_{p^2} \times C_p, there are three isom types of semidirect products of P \ltimes Q
          class2 := function(p, q)
            local list, G1, G2, G3;
              list := [];
              G1 := function(p, q) ## G1 exists only when p divides (q - 1)
                local c, r, data;
                  c := Z(q);
                  r := Int(c^((q-1)/p));
                  data := [ [p, p, p, q], [1, [2, 1]], [4, 3, [4, r]] ];
                return msg.groupFromData(data);
              end;
              ##
              if (q - 1) mod p = 0 then Add(list, G1(p, q)); fi;
              ##
              G2 := function(p, q) ## G2 exists only when p divides (q - 1)
                local c, r, data;
                  c := Z(q);
                  r := Int(c^((q-1)/p));
                  data := [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, r]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod p = 0 then Add(list, G2(p, q)); fi;

              G3 := function(p, q) ## G3 exists only when p^2 divides (q - 1)
                local c, r1, r2, data;
                  c := Z(q);
                  r1 := Int(c^((q-1)/p));
                  r2 := Int(c^((q-1)/(p^2)));
                  data := [ [p, p, p, q], [1, [2, 1]], [4, 1, [4, r2]], [4, 2, [4, r1]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod (p^2) = 0 then Add(list, G3(p, q)); fi;

            return list;
          end;

          Append(l, class2(p, q));

          ## class 3: when P is elementary abelian, there is a unique isom type of P \ltimes Q
          class3 := function(p, q) ##class 3 exists only when p divides (q - 1)
            local data, c, r;
              c := Z(q);
              r := Int(c^((q-1)/p));
              data := [ [p, p, p, q], [4, 1, [4, r]] ];
            return msg.groupFromData(data);
          end;

          if (q - 1) mod p = 0 then
            Add(l, class3(p, q));
          fi;

          ## class 4: when P is extraspecial + type, there is a unique isom type of P \ltimes Q
          class4 := function(p, q)
            local list, G1, G2;
              list := [];
              G1 := function(p, q)
                local c, r, data;
                  c := Z(q);
                  r := Int(c^((q-1)/p));
                  data := [[p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [4, r]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod p = 0 then
                Add(list, G1(p, q));
              fi;

              G2 := function(q)
                local data;
                  data := [ [2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q-1]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod p = 0 and p = 2 then
                Add(list, G2(q));
              fi;

            return list;
          end;
          if (q - 1) mod p = 0 then
            Append(l, class4(p, q)); fi;
          ## class 5: when P is extraspecial - type, there is a unique isom type of P \ltimes Q
          class5 := function(p, q)
            local list, t, G1, G2;
              list := [];
              G1 := function(k, p, q)
                local c, r, data;
                  c := Z(q);
                  r := Int(c^(k*(q-1)/p));
                  data := [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, r]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod p = 0 and p > 2 then for t in [1..p-1]
                do Add(list, G1(t, p, q));
                od;
              fi;

              G2 := function(p, q)
                local c, r, data;
                  c := Z(q);
                  r := Int(c^((q-1)/p));
                  data := [ [p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 2, [4, r]] ];
                return msg.groupFromData(data);
              end;

              if (q - 1) mod p = 0 and p > 2 then
                Add(list, G2(p, q)); fi;
            return list;
          end;

          if (q - 1) mod p = 0 and p > 2 then
            Append(l, class5(p, q)); fi;
          ## class 6: when P = Q_8, there is a unique isom type of P \ltimes Q
          class6 := function(q)
            local data;
              data := [ [2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [4, q - 1]] ];
            return msg.groupFromData(data);
          end;

        if p = 2 and q > p then
          Add(l, class6(q)); fi;

        return l;
    end;
############ case 3 exists only when (q - 1) mod p = 0
    if (q - 1) mod p = 0 then Append(s, case3(p, q)); fi;
## all above checked for x in Filtered(Primes, x-> x>8) do Print("checked ", x, ", ", testMySmallGroups(8*x), "\n"); od;

############ case 4: nonabelian and only the Sylow p-subgroup is normal
    case4 := function(p, q)
      local class1, class2, class3, class4, class5, class6, class7, l; ## classes depending on the isom type of P
        l := [];
        ## class 1: when P is cyclic, there is a unique isom type of semidirect products of Q \ltimes P
        class1 := function(p, q)
          local i, ii, q1, r3, a, b, data;
            a := ZmodnZObj(Int(Z(p)), p^3);
            if not a^(p - 1) = ZmodnZObj(1, p^2) then
              b := a;
            else b := a+1; fi;
            r3 := Int(b^((p^3 - p^2)/q));
            i := r3 mod p;
            ii := (r3 - i)/p mod p;
            q1 := ((r3 - i)/p - ii)/p;
            data := [ [q, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, i, 3, ii, 4, q1]], [3, 1, [3, i, 4, ii]], [4, 1, [4, i]] ];
          return msg.groupFromData(data);
        end;

        if (p - 1) mod q = 0 then
          Add(l, class1(p, q)); fi;

        ## class 2: when P = C_{p^2} \times C_p, there are (q + 1) isomorphism types of Q \ltimes P
        class2 := function(p, q)
          local list, G1, G2, G3, t;
            list := [];
            G1 := function(p, q)  ## C_q \ltimes C_p \times C_{p^2}
              local data, c, r;
                c := Z(p);
                r := Int(c^((p-1)/q));
                data := [ [q, p, p, p], [3, [4, 1]], [2, 1, [2, r]] ];
              return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

            G2 := function(p, q)  ## C_q \ltimes C_{p^2} \times C_p
              local data, a, b, r, ii, qq;
                a := ZmodnZObj(Int(Z(p)),p^2);
                if not a^(p - 1) = ZmodnZObj(1, p^2) then
                  b := a;
                else b := a + 1; fi;
                r := Int(b^((p^2-p)/q));
                ii := r mod p;
                qq := (r - ii)/p;
                data := [ [q, p, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ];
              return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 then Add(list, G2(p, q)); fi;

            G3 := function(k, p, q)  ## C_q \ltimes (C_{p^2} \times C_p)
              local data, a, b, r, rr, ii, qq;
                a := ZmodnZObj(Int(Z(p)), p^2);
                if not a^(p - 1) = ZmodnZObj(1, p^2) then
                  b := a;
                else b := a+1; fi;
                r := Int(b^(k*(p^2-p)/q));
                rr := (Int(b^((p^2-p)/q))) mod p;
                ii := r mod p;
                qq := (r - ii)/p;
                data := [ [q, p, p, p], [ 2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, rr]] ];
              return msg.groupFromData(data);
            end;


            if (p - 1 ) mod q = 0 then
              for t in [1..(q - 1)] do
                Add(list, G3(t, p, q));
              od;
            fi;

          return list;
        end;

        if (p - 1) mod q = 0 then
            Append(l, class2(p, q)); fi;

        ## class 3: when P is elementary abelian
        class3 := function(p, q)
          local list, G1, G2, G3, G4, G5, t;
            list := [];
            G1 := function(p, q) ## C_q \ltimes C_p \times C_p^2
              local c, r, data;
                c := Z(p);
                r := Int(c^((p - 1)/q));
                data := [ [q, p, p, p], [4, 1, [4, r]] ];
              return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

            G2 := function(k, p, q) ## (C_q \ltimes C_p^2) \times C_p when q | (p - 1)
              local r, a, l, j, i, data;
                r:= Z(p);
                a:= Int(r^((p-1)/q));
                l:= Z(q);
                i:= Int(l^k);
           			j:= Int(r^(i*(p-1)/q));
                data := [ [q, p, p, p], [2, 1, [2, a]], [3, 1, [3, j]] ];
           		return msg.groupFromData(data);
           	end;

            if (p - 1) mod q = 0 and q > 2 then for t in [0..(q-1)/2] do Add(list, G2(t, p, q)); od; fi;
            if q = 2 then Add(list, G2(0, p, 2)); fi;

            G3 := function(p, q) ## (C_q \ltimes C_p^2) \times C_p when q | (p + 1)
              local mat, data;
              	mat := msg.QthRootGL2P(p, q);
                data := [ [q, p, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ];
              return msg.groupFromData(data);
            end;

            if (p + 1) mod q = 0 and q > 2 then Add(list, G3(p, q)); fi;

            G4 := function(p, q) ## (C_q \ltimes C_p^3) when q | (p - 1)
              local a, r, t, tmp, data1, data2, data3, func, data4;
                tmp :=[];
                a := Int(Z(p)^((p-1)/q));
                r := Z(q);
                data1 := function(i)
                  local x, k, data;
                    x := Int(r^i);
                    k := Int(Z(p)^(x*(p - 1)/q));
                    data := [ [q, p, p ,p], [2, 1, [2, a]], [3, 1, [3, a]], [4, 1, [4, k]] ];
                  return msg.groupFromData(data);
                end;

                if q = 2 then Add(tmp, data1(0)); fi;
                if (p - 1) mod 3 = 0 and q = 3 then
                  for t in [0, 1] do Add(tmp, data1(t)); od; fi;
                if (p - 1) mod q = 0 and q > 3 then
                  for t in Filtered([1..(q - 2)], x-> not x = (q - 1)/2)
                    do Add(tmp, data1(t)); od; fi;

                data2 := function(i)
                  local data, x, y, k, k2;
                    x := Int(r^i);
                    y := Int(r^(-i));
                    k := Int(Z(p)^(x*(p-1)/q));
                    k2 := Int(Z(p)^(y*(p-1)/q));
                    data := [ [q, p, p, p], [2, 1, [2, a]], [3, 1, [3, k]], [4, 1, [4, k2]] ];
                  return msg.groupFromData(data);
                end;

                if (p - 1) mod q = 0 and q mod 3 = 1 then
                  for t in Filtered([1..(q - 1)/2], x->not x = (q - 1)/3 and not x = 2*(q - 1)/3)
                    do Add(tmp, data2(t)); od; fi;
                if (p - 1) mod q = 0 and q mod 3 = 2 and q > 2 then
                  for t in [1..(q - 1)/2]
                    do Add(tmp, data2(t)); od; fi;

                data3 := function(i)
                  local data, x, y, k, k2;
                    x := Int(r^i);
                    y := Int(r^(-i));
                    k := Int(Z(p)^(x*(p-1)/q));
                    k2 := Int(Z(p)^(y*(p-1)/q));
                    data := [ [q, p, p, p], [2, 1, [2, a]], [3, 1, [3, k]], [4, 1, [4, k2]] ];
                  return msg.groupFromData(data);
                end;

                if (p - 1) mod q = 0 and q mod 3 = 1 then for t in [0, (q - 1)/3] do Add(tmp, data3(t)); od; fi;
                if (p - 1) mod q = 0 and q > 3 and q mod 3 = 2 then Add(tmp, data3(0)); fi;

                func := function(q)
                  local i, j, ll, aa, bb, m;
                    ll := [];
                    if q mod 3 = 1 then m := (2*q - 5)/3;
                    else m := (2*q - 7)/3; fi;
                    for i in [1..m]
                      do for j in [i+1..q - 2]
                        do  aa := 2*(q - 1) - i - j;
                            bb := aa - (q - 1);
                          if (j < bb and bb < q - 1) or (j < aa and aa < q - 1) then
                            Add(ll, [-i mod (q - 1), j]);
                          fi;
                        od;
                      od;
                  return ll;
                end;

                data4 := function(i)
                  local data, x, y, k, k2;
                  x := Int(r^(i[1]));
                  y := Int(r^(i[2]));
                  k := Int(Z(p)^(x*(p - 1)/q));
                  k2 := Int(Z(p)^(y*(p - 1)/q));
                  data := [ [q, p, p, p], [2, 1, [2, a]], [3, 1, [3, k]], [4, 1, [4, k2]] ];
                return msg.groupFromData(data);
              end;

              if (p - 1) mod q = 0 and q > 3 then for t in func(q) do Add(tmp, data4(t)); od; fi;

              return tmp;
            end;

            if (p - 1) mod q = 0 then Append(list, G4(p, q)); fi;

            G5 := function(p, q) ## (C_q \ltimes C_p^3) when q | (p^2 + p + 1)
              local mat, data;
                mat := msg.QthRootGL3P(p, q);
                data := [ [q, p, p, p],
                [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1]), 4, Int(mat[3][1])]],
                [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2]), 4, Int(mat[3][2])]],
                [4, 1, [2, Int(mat[1][3]), 3, Int(mat[2][3]), 4, Int(mat[3][3])]] ];
               return msg.groupFromData(data);
            end;

            if (p^2 + p + 1 ) mod q = 0 and q > 3 then Add(list, G5(p, q)); fi;
          return list;
        end;

        if (p^3 - 1) mod q = 0 or (p^2 - 1) mod q = 0 then
        Append(l, class3(p, q)); fi;

        class4 := function(p, q) ##when P is extraspecial of type +,
          local list, t, r, a, G1, G2, G3, G4, G5;
            list := [];
            r := Z(p);
            if (p - 1) mod q = 0 then
              a := Int(r^((p-1)/q));
            fi;
            G1 := function(p, q) ## q | (p - 1), Z(G) = C_p
              local data, b;
                b := Int(r^((1-p)/q));
                data := [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [3, 1, [3, a]], [2, 1, [2, b]] ];
              return msg.groupFromData(data);
            end;
            if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

            G2 := function(p, q) ## q | (p - 1), Z(G) = 1
              local data;
                data := [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, a]], [2, 1, [2, a]] ];
               return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 then Add(list, G2(p, q)); fi;

            G3 := function(i, p, q) ## q | (p - 1), Z(G) = 1
              local b, c, data;
                b := Int(r^(i*(p-1)/q));
                c := Int(r^((q+1-i)*(p-1)/q));
                data := [ [q, p, p, p], [3, 2, [3, 1, 4, 1]], [4, 1, [4, a]], [3, 1, [3, b]], [2, 1, [2, c]] ];
               return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 and q > 2 then for t in [2..(q + 1)/2] do
              Add(list, G3(t, p, q)); od; fi;

            G4 := function(p, q) ## q | (p + 1), Z(G) = C_p
              local data, mat;
                mat := msg.QthRootGL2P(p, q);
                data := [ [q, p, p, p],
                [3, 2, [3, 1, 4, 1]],
                [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]],
                [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ];
              return msg.groupFromData(data);
            end;

            if (p + 1) mod q = 0 and q > 2 and p > 2 then Add(list, G4(p, q)); fi;

          return list;
        end;

        if (p^2 - 1) mod q = 0 then
          Append(l, class4(p, q)); fi;

        class5 := function(p, q) ##when P is extraspecial of type -,
          local list, G1;
            list := [];
            G1 := function(p, q)
              local a, b, r, qq, ii, data;
                a := ZmodnZObj(Int(Z(p)),p^2);
                if not a^(p - 1) = ZmodnZObj(1,p^2) then
                  b := a;
                else b := a + 1; fi;
                r := Int(b^(p*(p-1)/q));
                ii := r mod p;
                qq := (r - ii)/p;
                data := [ [q, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ];
               return msg.groupFromData(data);
            end;

            if (p - 1) mod q = 0 then Add(list, G1(p, q)); fi;

            return list;
          end;

          if (p - 1) mod q = 0 then
            Append(l, class5(p, q)); fi;

        class6 := [ [3, 2, 2, 2], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ]; ## special cases for p = 2 and q = 3
        if p = 2 and q = 3 then
          Add(l, msg.groupFromData(class6)); fi;
      ##
      return l;
    end;
    ##
    Append(s, case4(p, q));
  return s;
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
          m := 5 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
            + msg.deltaDivisibility((q-1), p^3) + (36+q^2+13*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)/6
            + 2*msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((p^2+p+1), q);
          elif n mod 2 = 1 and q = 3 then
            m := 5 + (5+p)*msg.deltaDivisibility((q-1), p) + 2*msg.deltaDivisibility((q-1), p^2)
              + msg.deltaDivisibility((q-1), p^3) + (36+q^2+13*q+4*msg.deltaDivisibility((q-1),3))*msg.deltaDivisibility((p-1), q)/6
              + 2*msg.deltaDivisibility((p+1), q);
            else m := 5 + 7*msg.deltafunction(p,2) + 2*msg.deltaDivisibility((q-1),4) + msg.deltaDivisibility((q-1), 8)
              + 10*msg.deltafunction(q,2) + 3*msg.deltafunction(n,24) + msg.deltafunction(n,56); fi;
        return m;
      end;
######################################################
msg.isp3q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i->  i[2]) in [ [ 3, 1 ], [ 1, 3 ] ];
