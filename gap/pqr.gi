
deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
    ###################################
InstallGlobalFunction( allGroupsPQR, function(n)
    local fac, p, q, r, coll, G1, G2, G3, G4, G5, G6, s;
      s := [];
      fac := Factors(n);
      if not Length(fac) = 3 then
        Error("Argument must be a product of three distinct primes"); fi;
      r := fac[1];
      q := fac[2];
      p := fac[3];
      G1 := function(p, q, r) #(C_r \ltimes C_q) \times C_p
        local G, coll;
          coll := FromTheLeftCollector(3);
          SetRelativeOrder(coll, 1, r);
          SetRelativeOrder(coll, 2, q);
          SetRelativeOrder(coll, 3, p);
          G := PcpGroupByCollector(coll);
        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
      end;
      Add(s, G1);
      
      if not (p - 1) mod q = 0 and not (p - 1) mod r = 0 and not (q - 1) mod r = 0 then
        return s; fi;

      G2 := function(p, q, r) #(C_r \ltimes C_q) \times C_p
        local G, coll, s;
          s := Int((Z(q))^((q-1)/r));
          coll := FromTheLeftCollector(3);
          SetRelativeOrder(coll, 1, r);
          SetRelativeOrder(coll, 2, q);
          SetRelativeOrder(coll, 3, p);
          SetConjugate(coll, 2, 1, [2, s]);
          G := PcpGroupByCollector(coll);
        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
      end;
      if (q - 1) mod r = 0 then
        Add(s, G2(p, q, r));fi;

        G3 := function(p, q, r) #(C_r \ltimes C_p) \times C_q
          local G, coll, t;
            t := Int((Z(p))^((p-1)/r));
            coll := FromTheLeftCollector(3);
            SetRelativeOrder(coll, 1, r);
            SetRelativeOrder(coll, 2, q);
            SetRelativeOrder(coll, 3, p);
            SetConjugate(coll, 3, 1, [3, t]);
            G := PcpGroupByCollector(coll);
          return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
        end;
        if (p - 1) mod r = 0 then
          Add(s, G3(p, q, r));fi;

          G4 := function(p, q, r) #C_r \ltimes (C_q \times C_p)
            local G, coll, s, t;
              s := Int((Z(q))^((q-1)/r));
              t := Int((Z(p))^((p-1)/r));
              coll := FromTheLeftCollector(3);
              SetRelativeOrder(coll, 1, r);
              SetRelativeOrder(coll, 2, q);
              SetRelativeOrder(coll, 3, p);
              SetConjugate(coll, 2, 1, [2, s]);
              SetConjugate(coll, 3, 1, [3, t]);
              G := PcpGroupByCollector(coll);
            return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
          end;
          if (q - 1) mod r = 0 and (p - 1) mod r = 0 then
            Add(s, G4(p, q, r));fi;

            G5 := function(p, q, r) #C_r \times (C_q \ltimes C_p)
              local G, coll, o;
                o := Int((Z(p))^((p-1)/q));
                coll := FromTheLeftCollector(3);
                SetRelativeOrder(coll, 1, r);
                SetRelativeOrder(coll, 2, q);
                SetRelativeOrder(coll, 3, p);
                SetConjugate(coll, 3, 2, [3, o]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
            if (p - 1) mod q = 0 then
              Add(s, G5(p, q, r));fi;

            G6 := function(p, q, r) #C_r \times (C_q \ltimes C_p)
              local G, coll, o, t;
                o := Int((Z(p))^((p-1)/q));
                t := Int((Z(p))^((p-1)/r));
                coll := FromTheLeftCollector(3);
                SetRelativeOrder(coll, 1, r);
                SetRelativeOrder(coll, 2, q);
                SetRelativeOrder(coll, 3, p);
                SetConjugate(coll, 3, 1, [3, t]);
                SetConjugate(coll, 3, 2, [3, o]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
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
        w := 1 + (2 + deltaDivisibility((p-1), q))*(deltaDivisibility((p - 1), r)) + deltaDivisibility((q - 1), r) + deltaDivisibility((p - 1), q);
      return w;
    end;
