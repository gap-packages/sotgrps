
deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
    ###################################
InstallGlobalFunction( allGroupsPQR, function(n)
    local fac, p, q, r, coll, G1, G2, G3, G4, G5, G6, s, i;
      s := [];
      fac := Factors(n);
      if not Length(fac) = 3 then
        Error("Argument must be a product of three distinct primes"); fi;
      r := fac[1];
      q := fac[2];
      p := fac[3];
      G1 := function(p, q, r) #(C_r \ltimes C_q) \times C_p
        local data;
          data := [ [r, q, p] ];
        return msg.groupFromData(data);
      end;
      Add(s, G1(p, q, r));

      if not (p - 1) mod q = 0 and not (p - 1) mod r = 0 and not (q - 1) mod r = 0 then
        return s; fi;

      G2 := function(p, q, r) #(C_r \ltimes C_q) \times C_p
        local s, data;
          s := Int((Z(q))^((q-1)/r));
          data := [ [r, q, p], [2, 1, [2, s]] ];
        return msg.groupFromData(data);
      end;
      if (q - 1) mod r = 0 then
        Add(s, G2(p, q, r));fi;

        G3 := function(p, q, r) #(C_r \ltimes C_p) \times C_q
          local t, data;
            t := Int((Z(p))^((p-1)/r));
            data := [ [r, q, p], [3, 1, [3, t]] ];
          return msg.groupFromData(data);
        end;
        if (p - 1) mod r = 0 then
          Add(s, G3(p, q, r));fi;

          G4 := function(p, q, r, k) #C_r \ltimes (C_q \times C_p)
            local data, s, t;
              s := (Z(q))^((q-1)/r);
              t := (Z(p))^((p-1)/r);
              data := [ [r, q, p], [2, 1, [2, Int(s)]], [3, 1, [3, Int(t^k)]] ];
            return msg.groupFromData(data);
          end;
          ##
          if (q - 1) mod r = 0 and (p - 1) mod r = 0 then
            for i in [1..(r - 1)] do
              Add(s, G4(p, q, r, i));
            od;
          fi;
          ##

            G5 := function(p, q, r) #C_r \times (C_q \ltimes C_p)
              local data, o;
                o := Int((Z(p))^((p-1)/q));
                data := [ [r, q, p], [3, 2, [3, o]] ];
              return msg.groupFromData(data);
            end;
            if (p - 1) mod q = 0 then
              Add(s, G5(p, q, r));fi;

            G6 := function(p, q, r) #(C_r \times C_q) \ltimes C_p
              local data, o, t;
                o := Int((Z(p))^((p-1)/q));
                t := Int((Z(p))^((p-1)/r));
                data := [ [r, q, p], [3, 1, [3, t]], [3, 2, [3, o]] ];
              return msg.groupFromData(data);
            end;
            if (p - 1) mod r = 0 and (p - 1) mod q = 0 then
              Add(s, G6(p, q, r));fi;
      return s;
    end);

    ##############################################
    NumberGroupsPQR := function(n)
      local fac, p, q, r, w;
        fac := Factors(n);
        if not Length(fac) = 3 then
          Error("Argument must be a product of two distinct primes"); fi;
        r := fac[1];
        q := fac[2];
        p := fac[3];
        w := 1 + deltaDivisibility((q-1), r) + deltaDivisibility((p - 1), r) + (r - 1) * deltaDivisibility((q - 1), r) * deltaDivisibility((p - 1), r) + deltaDivisibility((p - 1), q) + deltaDivisibility((p - 1), r) * deltaDivisibility((p - 1), q);
      return w;
    end;
