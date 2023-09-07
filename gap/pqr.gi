## Construction of squarefree groups of order pqr.
## The classification of these groups follows from the following theorem by Hoelder, Burnside, and Zassenhaus:
## THEOREM:
  ## Let G be a group of order n whose Sylow subgroups are cyclic. Then G is metacyclic with odd-order derived subgroup [G, G] \cong C_b and cyclic quotient G/[G, G] \cong C_a, where a = n/b.
  ## In particular, G is isomorphic to <x, y | x^a, y^b, y^x = y^r > for some non-negative integer r such that r^a = 1 mod b, and gcd(a(r - 1), b) = 1.

##############################################
SOTRec.allGroupsPQR := function(p, q, r)
local a, b, rootpq, rootpr, rootqr, all, k;
    ## r < q < p
    ####
    Assert(1, p > q and q > r);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    ####precompute roots:
    a := Z(p);
    b := Z(q);

    if (p - 1) mod r = 0 then
      rootpr := Int(a^((p-1)/r));
    fi;
    if (p - 1) mod q = 0 then
      rootpq := Int(a^((p-1)/q));
    fi;
    if (q - 1) mod r = 0 then
      rootqr := Int(b^((q-1)/r));
    fi;

    all := [ [ [r, q, p] ] ]; #(C_r \ltimes C_q) \times C_p
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if (q - 1) mod r = 0 then
        Add(all, [ [r, q, p], [2, 1, [2, rootqr]] ]);
    fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_r) \times C_p
    if (p - 1) mod r = 0 then
        Add(all, [ [r, q, p], [3, 1, [3, rootpr]] ]);
    fi;
    ####case 3: q | (p - 1) and Z(G) \cong C_r, G \cong C_r \times (C_q \ltimes C_p)
    if (p - 1) mod q = 0 then
        Add(all, [ [r, q, p], [3, 2, [3, rootpq]] ]);
    fi;
    ####case 4: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \ltimes C_p)
    if (q - 1) mod r = 0 and (p - 1) mod r = 0 then
        for k in [1..(r - 1)] do
            Add(all, [ [r, q, p], [2, 1, [2, rootqr]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
      od;
    fi;
    ####case 5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if (p - 1) mod r = 0 and (p - 1) mod q = 0 then
        Add(all, [ [r, q, p], [3, 1, [3, rootpr]], [3, 2, [3, rootpq]] ]);
    fi;

  return List(all, x-> SOTRec.groupFromData(x));
end;
##############################################
SOTRec.NumberGroupsPQR := function(p, q, r)
local w;
    ## r < q < p
    ####
    Assert(1, p > q and q > r);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    w := 1 + SOTRec.w((q-1), r)
           + SOTRec.w((p - 1), r) + (r - 1) * SOTRec.w((q - 1), r) * SOTRec.w((p - 1), r)
           + SOTRec.w((p - 1), q) + SOTRec.w((p - 1), r) * SOTRec.w((p - 1), q);
    return w;
end;
##############################################
SOTRec.GroupPQR := function(p, q, r, i)
local all, a, b, k, c1, c2, c3, c4, c5, rootpq, rootpr, rootqr;
    ## r < q < p
    ####
    Assert(1, p > q and q > r);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    #abelian groups
    all := [ [ [r, q, p] ] ];
    if i = 1 then
      return SOTRec.groupFromData(all[1]);
    fi;
    ####precompute roots:
    a := Z(p);
    b := Z(q);

    if (p - 1) mod r = 0 then
      rootpr := Int(a^((p-1)/r));
    fi;
    if (p - 1) mod q = 0 then
      rootpq := Int(a^((p-1)/q));
    fi;
    if (q - 1) mod r = 0 then
      rootqr := Int(b^((q-1)/r));
    fi;
    ####enumeration
    c1 := SOTRec.w((q - 1), r);
    c2 := SOTRec.w((p - 1), r);
    c3 := SOTRec.w((p - 1), q);
    c4 := (r - 1)*SOTRec.w((q - 1), r) * SOTRec.w((p - 1), r);
    c5 := SOTRec.w((p - 1), q*r);
    ####case 1: r | (q - 1), Z(G) \cong C_p, G \cong (C_r \ltimes C_q) \times C_p
    if i > 1 and i < 2 + c1 and (q - 1) mod r = 0 then
        return SOTRec.groupFromData([ [r, q, p], [2, 1, [2, rootqr]] ]);
    fi;
    ####case 2: r | (p - 1), Z(G) \cong C_q, G \cong (C_r \ltimes C_p) \times C_q
    if i > 1 + c1 and i < 2 + c1 + c2 and (p - 1) mod r = 0 then
        Add(all, [ [r, q, p], [3, 1, [3, rootpr]] ]);
        return SOTRec.groupFromData(all[i - c1]);
    fi;

    ####case 3: q | (p - 1) and Z(G) \cong C_r, G \cong C_r \times (C_q \ltimes C_p)
    if i > 1 + c1 + c2 and i < 2 + c1 + c2 + c3 and (p - 1) mod q = 0 then
        Add(all, [ [r, q, p], [3, 2, [3, rootpq]] ]);
        return SOTRec.groupFromData(all[i - c1 - c2]);
    fi;

    ####case 4: r | (p - 1) and r |(q - 1), and Z(G) = 1, G \cong C_r \ltimes (C_q \times C_p)
    if i > 1 + c1 + c2 + c3 and i < 2 + c1 + c2 + c3 + c4 and (q - 1) mod r = 0 and (p - 1) mod r = 0 then
        for k in [1..(r - 1)] do
            Add(all, [ [r, q, p], [2, 1, [2, rootqr]], [3, 1, [3, Int(a^(k*(p-1)/r))]] ]);
        od;
        return SOTRec.groupFromData(all[i - c1 - c2 - c3]);
    fi;

    ####case5: r | (p - 1) and q | (p - 1), Z(G) = 1, and G \cong (C_r \times C_q) \ltimes C_p
    if i > 1 + c1 + c2 + c3 + c4 and i < 2 + c1 + c2 + c3 + c4 + c5 and  (p - 1) mod r = 0 and (p - 1) mod q = 0 then
        Add(all, [ [r, q, p], [3, 1, [3, rootpr]], [3, 2, [3, rootpq]] ]);
        return SOTRec.groupFromData(all[i - c1 - c2 - c3 - c4]);
    fi;

end;
