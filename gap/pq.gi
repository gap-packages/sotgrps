
deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
    ###################################
InstallGlobalFunction( allGroupsPQ, function(n)
    local fac, p, q, coll, r, nonabelian, s;
      s := [];
      fac := Factors(n);
      if Length(fac) > 2 then
        Error("Argument must be a product of two distinct primes"); fi;
      q := fac[1];
      p := fac[2];
      Add(s, AbelianGroup([n]));
      if not (p - 1) mod q = 0 then
        return s; fi;

      nonabelian := function(p, q)
        local G, coll, r;

        r := Int((Z(p))^((p-1)/q));
        coll := FromTheLeftCollector(2);
        SetRelativeOrder(coll, 1, q);
        SetRelativeOrder(coll, 2, p);
        SetConjugate(coll, 2, 1, [2, r]);


          G := PcpGroupByCollector(coll);

        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
      end;
      if (p - 1) mod q = 0 then
        Add(s, nonabelian(p, q));fi;
      return s;
    end);

    ##############################################
    NumberGroupsPQ := function(n)
      local fac, p, q, w;
        fac := Factors(n);
        if Length(fac) > 2 then
          Error("Argument must be a product of two distinct primes"); fi;
        q := fac[1];
        p := fac[2];

        w := 1 + deltaDivisibility((p - 1), q);
      return w;
    end;
