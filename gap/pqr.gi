msg.allGroupsPQR := function(n)
  local fac, p, q, r, a, b, coll, G1, G2, G3, G4, G5, G6, all, k;
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    a := Z(p);
    b := Z(q);

    all := [ [ [r, q, p] ] ]; #(C_r \ltimes C_q) \times C_p
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if (q - 1) mod r = 0 then
      Add(all, [ [r, q, p], [2, 1, [2, Int(b^((q-1)/r))]] ]);fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_r) \times C_p
    if (p - 1) mod r = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, Int(a^((p-1)/r))]] ]);fi;
    ####case3: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \ltimes C_p)
    if (q - 1) mod r = 0 and (p - 1) mod r = 0 then
      for k in [1..(r - 1)] do
        Add(all, [ [r, q, p], [2, 1, [2, Int(b^((q-1)/r))]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
      od;
    fi;
    ####case4: q | (p - 1) and Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 2, [3, Int(a^((p-1)/q))]] ]);fi;
    ####case5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if (p - 1) mod r = 0 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, Int(a^((p-1)/r))]], [3, 2, [3, Int(a^((p-1)/q))]] ]);fi;

  return List(all, x-> msg.groupFromData(x));
end;
##############################################
msg.NumberGroupsPQR := function(n)
  local fac, p, q, r, w;
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of two distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    w := 1 + msg.deltaDivisibility((q-1), r) + msg.deltaDivisibility((p - 1), r) + (r - 1) * msg.deltaDivisibility((q - 1), r) * msg.deltaDivisibility((p - 1), r) + msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p - 1), r) * msg.deltaDivisibility((p - 1), q);
  return w;
end;
##############################################
msg.GroupPQR := function(n, i)
  local fac, all, p, q, r, a, b, k, c1, c2, c3, c4, c5;
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    all := [ [ [r, q, p] ] ];
    if i = 1 then return msg.groupFromData(all[1]); fi;
    a := Z(p);
    b := Z(q);
    ####enumeration
    c1 := msg.deltaDivisibility((q - 1), r);
    c2 := msg.deltaDivisibility((p - 1), r);
    c3 := (r - 1)*msg.deltaDivisibility((q - 1), r) * msg.deltaDivisibility((p - 1), r);
    c4 := msg.deltaDivisibility((p - 1), q);
    c5 := msg.deltaDivisibility((p - 1), q*r);
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if i > 1 and i < 2 + c1 and (q - 1) mod r = 0 then
      return msg.groupFromData([ [r, q, p], [2, 1, [2, Int(b^((q-1)/r))]] ]);
    fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_p) \times C_q
    if i > 1 + c1 and i < 2 + c1 + c2 and (p - 1) mod r = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, Int(a^((p-1)/r))]] ]);
      return msg.groupFromData(all[i - c1]);
    fi;

    ####case3: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \ltimes C_p)
    if i > 1 + c1 + c2 and i < 2 + c1 + c2 + c3 and (q - 1) mod r = 0 and (p - 1) mod r = 0 then
      for k in [1..(r - 1)] do
        Add(all, [ [r, q, p], [2, 1, [2, Int(b^((q-1)/r))]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
      od;
      return msg.groupFromData(all[i - c1 - c2]);
    fi;

    ####case4: q | (p - 1) and Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if i > 1 + c1 + c2 + c3 and i < 2 + c1 + c2 + c3 + c4 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 2, [3, Int(a^((p-1)/q))]] ]);
      return msg.groupFromData(all[i - c1 - c2 - c3]);
    fi;

    ####case5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if i > 1 + c1 + c2 + c3 + c4 and i < 2 + c1 + c2 + c3 + c4 + c5 and  (p - 1) mod r = 0 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, Int(a^((p-1)/r))]], [3, 2, [3, Int(a^((p-1)/q))]] ]);
      return msg.groupFromData(all[i - c1 - c2 - c3 - c4]);
    fi;

end;
