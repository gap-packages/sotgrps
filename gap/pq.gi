
deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
    ###################################
InstallGlobalFunction( allGroupsPQ, function(n)
    local fac, p, q, abelian, nonabelian, s;
      s := [];

      fac := Factors(n);
      if Length(fac) > 2 then
        Error("Argument must be a product of two distinct primes"); fi;
      q := fac[1];
      p := fac[2];

      abelian := [ [p, q] ];

      Add(s, msg.groupFromData(abelian));

      if not (p - 1) mod q = 0 then
        return s; fi;

      if (p - 1) mod q = 0 then
        nonabelian := [ [q, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ];
        Add(s, msg.groupFromData(nonabelian));fi;
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
