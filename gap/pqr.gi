## Construction of squarefree groups of order pqr.
## The classification of these groups follows from the following theorem by Hoelder, Burnside, and Zassenhaus:
## THEOREM:
  ## Let G be a group of order n whose Sylow subgroups are cyclic. Then G is metacyclic with odd-order derived subgroup [G, G] \cong C_b and cyclic quotient G/[G, G] \cong C_a, where a = n/b.
  ## In particular, G is isomorphic to <x, y | x^a, y^b, y^x = y^r > for some non-negative integer r such that r^a = 1 mod b, and gcd(a(r - 1), b) = 1.

##############################################
msg.allGroupsPQR := function(n)
  local fac, p, q, r, a, b, rootpq, rootpr, rootqr, all, k;
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    ####precompute roots:
    a := Z(p);
    b := Z(q);

    if (p - 1) mod r = 0 then rootpr := Int(a^((p-1)/r)); fi;
    if (p - 1) mod q = 0 then rootpq := Int(a^((p-1)/q)); fi;
    if (q - 1) mod r = 0 then rootqr := Int(b^((q-1)/r)); fi;

    all := [ [ [r, q, p] ] ]; #(C_r \ltimes C_q) \times C_p
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if (q - 1) mod r = 0 then
      Add(all, [ [r, q, p], [2, 1, [2, rootqr]] ]);fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_r) \times C_p
    if (p - 1) mod r = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, rootpr]] ]);fi;
    ####case3: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \ltimes C_p)
    if (q - 1) mod r = 0 and (p - 1) mod r = 0 then
      for k in [1..(r - 1)] do
        Add(all, [ [r, q, p], [2, 1, [2, rootqr]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
      od;
    fi;
    ####case4: q | (p - 1) and Z(G) \cong C_r, G \cong C_r \times (C_q \ltimes C_p)
    if (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 2, [3, rootpq]] ]);fi;
    ####case5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if (p - 1) mod r = 0 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, rootpr]], [3, 2, [3, rootpq]] ]);fi;

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
    w := 1 + msg.w((q-1), r) + msg.w((p - 1), r) + (r - 1) * msg.w((q - 1), r) * msg.w((p - 1), r) + msg.w((p - 1), q) + msg.w((p - 1), r) * msg.w((p - 1), q);
  return w;
end;
##############################################
msg.GroupPQR := function(n, i)
  local fac, all, p, q, r, a, b, k, c1, c2, c3, c4, c5, rootpq, rootpr, rootqr;
    fac := Factors(n);
    if not Length(fac) = 3 then
      Error("Argument must be a product of three distinct primes"); fi;
    r := fac[1];
    q := fac[2];
    p := fac[3];
    all := [ [ [r, q, p] ] ];
    if i = 1 then return msg.groupFromData(all[1]); fi;
    ####precompute roots:
    a := Z(p);
    b := Z(q);

    if (p - 1) mod r = 0 then rootpr := Int(a^((p-1)/r)); fi;
    if (p - 1) mod q = 0 then rootpq := Int(a^((p-1)/q)); fi;
    if (q - 1) mod r = 0 then rootqr := Int(b^((q-1)/r)); fi;
    ####enumeration
    c1 := msg.w((q - 1), r);
    c2 := msg.w((p - 1), r);
    c3 := (r - 1)*msg.w((q - 1), r) * msg.w((p - 1), r);
    c4 := msg.w((p - 1), q);
    c5 := msg.w((p - 1), q*r);
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if i > 1 and i < 2 + c1 and (q - 1) mod r = 0 then
      return msg.groupFromData([ [r, q, p], [2, 1, [2, rootqr]] ]);
    fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_p) \times C_q
    if i > 1 + c1 and i < 2 + c1 + c2 and (p - 1) mod r = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, rootpr]] ]);
      return msg.groupFromData(all[i - c1]);
    fi;

    ####case3: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \times C_p)
    if i > 1 + c1 + c2 and i < 2 + c1 + c2 + c3 and (q - 1) mod r = 0 and (p - 1) mod r = 0 then
      for k in [1..(r - 1)] do
        Add(all, [ [r, q, p], [2, 1, [2, rootqr]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
      od;
      return msg.groupFromData(all[i - c1 - c2]);
    fi;

    ####case4: q | (p - 1) and Z(G) \cong C_r, G \cong C_r \times (C_q \ltimes C_p)
    if i > 1 + c1 + c2 + c3 and i < 2 + c1 + c2 + c3 + c4 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 2, [3, rootpq]] ]);
      return msg.groupFromData(all[i - c1 - c2 - c3]);
    fi;

    ####case5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if i > 1 + c1 + c2 + c3 + c4 and i < 2 + c1 + c2 + c3 + c4 + c5 and  (p - 1) mod r = 0 and (p - 1) mod q = 0 then
      Add(all, [ [r, q, p], [3, 1, [3, rootpr]], [3, 2, [3, rootpq]] ]);
      return msg.groupFromData(all[i - c1 - c2 - c3 - c4]);
    fi;

end;
