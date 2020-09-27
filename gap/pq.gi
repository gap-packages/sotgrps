msg.allGroupsPQ := function(n)
  local fac, p, q, abelian, nonabelian, s;
    s := [];
    fac := Factors(n);
    if Length(fac) > 2 then
      Error("Argument must be a product of two distinct primes."); fi;
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
end;

##############################################
msg.NumberGroupsPQ := function(n)
  local fac, p, q, w;
    fac := Factors(n);
    if Length(fac) > 2 then
      Error("Argument must be a product of two distinct primes."); fi;
    q := fac[1];
    p := fac[2];
    w := 1 + msg.w((p - 1), q);
  return w;
end;
##############################################
msg.GroupPQ := function(n, i)
  local fac, p, q, all, G;
    fac := Factors(n);
    if Length(fac) > 2 then
      Error("Argument must be a product of two distinct primes."); fi;
    q := fac[1];
    p := fac[2];
    all := [ [ [p, q] ] ];
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ]);
    fi;

    if i < 2 + msg.w((p - 1), q) then
      G := msg.groupFromData(all[i]);
    fi;
  return G;
end;
