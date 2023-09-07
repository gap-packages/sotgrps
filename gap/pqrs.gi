## Construction of squarefree groups of order pqrs.
## The classification of these groups follows from the following theorem by Hoelder, Burnside, and Zassenhaus:
## Let G be a group of order n whose Sylow subgroups are cyclic. Then G is metacyclic with odd-order derived subgroup [G, G] \cong C_b and cyclic quotient G/[G, G] \cong C_a, where a = n/b.
## In particular, G is isomorphic to <x, y | x^a, y^b, y^x = y^r > for some non-negative integer r such that r^a = 1 mod b, and gcd(a(r - 1), b) = 1.

##############################################
######################################################
SOTRec.NumberGroupsPQRS := function(p, q, r, s)
local m;
    ####
    Assert(1, s > r and r > q and q > p);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    Assert(1, IsPrimeInt(s));
    ####
    m := 1 + SOTRec.w((s - 1), p*q*r)
    + SOTRec.w((r - 1), p*q) + SOTRec.w((s - 1), p*q)
    + (p - 1)*(q - 1)*SOTRec.w((s - 1), p*q)*SOTRec.w((r - 1), p*q)
    + (p - 1)*(SOTRec.w((s - 1), p)*SOTRec.w((r - 1), p*q) + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p*q))
    + (q - 1)*(SOTRec.w((s - 1), q)*SOTRec.w((r - 1), p*q) + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p*q))
    + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p)
    + SOTRec.w((s - 1), p*r) + SOTRec.w((q - 1), p)*SOTRec.w((s - 1), r)
    + (p - 1)*SOTRec.w((s - 1), p*r)*SOTRec.w((q - 1), p)
    + SOTRec.w((s - 1), q*r)
    + SOTRec.w((q - 1), p)*(1 + (p - 1)*SOTRec.w((r - 1), p))
    + SOTRec.w((s - 1), p)*(1 + (p - 1)*SOTRec.w((q - 1), p))
    + SOTRec.w((r - 1), p)*(1 + (p - 1)*SOTRec.w((s - 1), p))
    + (p - 1)^2 * SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
    + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q) + (q - 1) * SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q)
    + SOTRec.w((s - 1), r);

  return m;
end;
######################################################
######################################################
SOTRec.allGroupsPQRS := function(p, q, r, s)
local all, u, v, w, k, l, rootsr, rootsq, rootsp, rootrq, rootrp, rootqp, tmp, listall;
    ####
    Assert(1, s > r and r > q and q > p);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    Assert(1, IsPrimeInt(s));
    ####

    ##Cluster 1: Abelian group, Z(G) = G
    all := [ [ [p, q, r, s] ] ];

    u := Z(q);
    v := Z(r);
    w := Z(s);

    ##Cluster 2: |Z(G)| \in {pq, pr, ps, qr, qs, rs}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
      ##class 1: |Z(G)| = pq, G \cong (C_r \ltimes C_s) \times Z(G)
      if (s - 1) mod r = 0 then
        rootsr := Int(w^((s - 1)/r));
        Add(all, [ [p, q, r, s], [4, 3, [4, rootsr]] ]);
      fi;
      ##class 2: |Z(G)| = pr, G \cong (C_q \ltimes C_s) \times Z(G)
      if (s - 1) mod q = 0 then
        rootsq := Int(w^((s - 1)/q));
        Add(all, [ [p, q, r, s], [4, 2, [4, rootsq]] ]);
      fi;
      ##class 3: |Z(G)| = ps, G \cong (C_q \ltimes C_r) \times Z(G)
      if (r - 1) mod q = 0 then
        rootrq := Int(v^((r - 1)/q));
        Add(all, [ [p, q, r, s], [3, 2, [3, rootrq]] ]);
      fi;
      ##class 4: |Z(G)| = qr, G \cong (C_p \ltimes C_s) \times Z(G)
      if (s - 1) mod p = 0 then
        rootsp := Int(w^((s - 1)/p));
        Add(all, [ [p, q, r, s], [4, 1, [4, rootsp]] ]);
      fi;
      ##class 5: |Z(G)| = qs, G \cong (C_p \ltimes C_r) \times Z(G)
      if (r - 1) mod p = 0 then
        rootrp := Int(v^((r - 1)/p));
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]] ]);
      fi;
      ##class 6: |ZG)| = rs, G \cong (C_p \ltimes C_q) \times Z(G)
      if (q - 1) mod p = 0 then
        rootqp := Int(u^((q - 1)/p));
        Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]] ]);
      fi;

    ##Cluster 3: |Z(G)| \in {p, q, r, s}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
      ##class 1: |Z(G)| = p, |H| = qrs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod q = 0 and (r - 1) mod q = 0 then
        for k in [1..(q - 1)] do
          Add(all, [ [q, r, s, p], [2, 1, [2, rootrq]], [3, 1, [3, Int(w^(k*(s - 1)/q))]] ]);
        od;
      fi;
      if (s - 1) mod q = 0 and (s - 1) mod r = 0 then
        Add(all, [ [q, r, s, p], [3, 1, [3, rootsq]], [3, 2, [3, rootsr]] ]);
      fi;
      ##class 2: |Z(G)| = q, |H| = prs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod p = 0 and (r - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, r, s, q], [2, 1, [2, rootrp]], [3, 1, [3, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (s - 1) mod r = 0 then
        Add(all, [ [p, r, s, q], [3, 1, [3, rootsp]], [3, 2, [3, rootsr]] ]);
      fi;
      ##class 3: |Z(G)| = r, |H| = pqs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod p = 0 and (q - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, s, r], [2, 1, [2, rootqp]], [3, 1, [3, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (s - 1) mod q = 0 then
        Add(all, [ [p, q, s, r], [3, 1, [3, rootsp]], [3, 2, [3, rootsq]] ]);
      fi;
      ##class 4: |Z(G)| = s, |H| = pqr, Z(H) = 1, G \cong H \times Z(G)
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [3, 1, [3, Int(v^(k*(r - 1)/p))]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]] ]);
      fi;

    ##Cluster 4: Z(G) = 1
      ##class 1: G' \cong C_{qrs}, G \cong C_p \ltimes C_{qrs}
      if (q - 1) mod p = 0 and (r - 1) mod p = 0 and (s - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          for l in [1..(p - 1)] do
            Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^(l*(s - 1)/p))]] ]);
          od;
        od;
      fi;

      ##class 2: G' \cong C_{rs}, G \cong C_{pq} \ltimes C_{rs}
      if (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          for l in [1..(q - 1)] do
            Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 1, [4, Int(w^(k*(s - 1)/p))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
          od;
        od;
      fi;
      if (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 then
        for l in [1..(q - 1)] do
          Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^(l*(r - 1)/q))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 1, [4, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 then
        for l in [1..(q - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (s - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [4, 2, [4, rootsq]] ]);
      fi;
      if (r - 1) mod q = 0 and (s - 1) mod p = 0 then
        Add(all, [ [p, q, r, s], [3, 2, [3, rootrq]], [4, 1, [4, rootsp]] ]);
      fi;

      ##class 3: G' \cong C_{qs}, G \cong C_{pr} \ltimes C_{qs}
      if (s - 1) mod r = 0 and (q - 1) mod p = 0 then
        Add(all, [ [p, r, q, s], [3, 1, [3, rootqp]], [4, 2, [4, rootsr]] ]);
      fi;
      if (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, r, q, s], [3, 1, [3, Int(u^(k*(q - 1)/p))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsr]] ]);
        od;
      fi;

      ##class 4: G' \cong C_s, G \cong C_{pqr} \ltimes C_s
      if (s - 1) mod (p*q*r) = 0 then
        Add(all, [ [p, q, r, s], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]], [4, 3, [4, rootsr]] ]);
      fi;
    listall := List(all, x -> SOTRec.groupFromData(x));
  return listall;
end;
######################################################
SOTRec.GroupPQRS := function(p, q, r, s, i)
local all, u, v, w, j, k, l, c1, c2, c3, rootsr, rootsq, rootsp, rootrq, rootrp, rootqp, tmp, data;
    ####
    Assert(1, s > r and r > q and q > p);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));
    Assert(1, IsPrimeInt(s));

    ##Cluster 1: Abelian group, Z(G) = G
    all := [ [ [p, q, r, s] ] ];

    u := Z(q);
    v := Z(r);
    w := Z(s);

    if (s - 1) mod r = 0 then
      rootsr := Int(w^((s - 1)/r));
    fi;
    if (s - 1) mod q = 0 then
      rootsq := Int(w^((s - 1)/q));
    fi;
    if (r - 1) mod q = 0 then
      rootrq := Int(v^((r - 1)/q));
    fi;
    if (s - 1) mod p = 0 then
      rootsp := Int(w^((s - 1)/p));
    fi;
    if (r - 1) mod p = 0 then
      rootrp := Int(v^((r - 1)/p));
    fi;
    if (q - 1) mod p = 0 then
      rootqp := Int(u^((q - 1)/p));
    fi;
    ##enumeration of each case by size of the centre
    c1 := SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)
        + SOTRec.w((s - 1), p) + SOTRec.w((r - 1), p) + SOTRec.w((q - 1), p);
    c2 := (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q) + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p) + SOTRec.w((r - 1), (p*q));
    c3 := (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
        + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
        + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
        + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
        + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
        + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p)
        + SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), (p*r))
        + SOTRec.w((s - 1), (p*q*r));

    if i = 1 then
      return SOTRec.groupFromData(all[1]);
    ##Cluster 2: |Z(G)| \in {pq, pr, ps, qr, qs, rs}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
    elif i > 1 and i < 2 + c1 then
      all := [];
      ##class 1: |Z(G)| = pq, G \cong (C_r \ltimes C_s) \times Z(G)
      if (s - 1) mod r = 0 then
        Add(all, [ [p, q, r, s], [4, 3, [4, rootsr]] ]);
      fi;
      ##class 2: |Z(G)| = pr, G \cong (C_q \ltimes C_s) \times Z(G)
      if (s - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [4, 2, [4, rootsq]] ]);
      fi;
      ##class 3: |Z(G)| = ps, G \cong (C_q \ltimes C_r) \times Z(G)
      if (r - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [3, 2, [3, rootrq]] ]);
      fi;
      ##class 4: |Z(G)| = qr, G \cong (C_p \ltimes C_s) \times Z(G)
      if (s - 1) mod p = 0 then
        Add(all, [ [p, q, r, s], [4, 1, [4, rootsp]] ]);
      fi;
      ##class 5: |Z(G)| = qs, G \cong (C_p \ltimes C_r) \times Z(G)
      if (r - 1) mod p = 0 then
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]] ]);
      fi;
      ##class 6: |ZG)| = rs, G \cong (C_p \ltimes C_q) \times Z(G)
      if (q - 1) mod p = 0 then
        Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]] ]);
      fi;
      data := all[i - 1];
      return SOTRec.groupFromData(data);

    ##Cluster 3: |Z(G)| \in {p, q, r, s}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
    elif i > 1 + c1 and i < 2 + c1 + c2 then
      all := [];
      ##class 1: |Z(G)| = p, |H| = qrs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod q = 0 and (r - 1) mod q = 0 then
        for k in [1..(q - 1)] do
          Add(all, [ [q, r, s, p], [2, 1, [2, rootrq]], [3, 1, [3, Int(w^(k*(s - 1)/q))]] ]);
        od;
      fi;
      if (s - 1) mod q = 0 and (s - 1) mod r = 0 then
        Add(all, [ [q, r, s, p], [3, 1, [3, rootsq]], [3, 2, [3, rootsr]] ]);
      fi;
      ##class 2: |Z(G)| = q, |H| = prs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod p = 0 and (r - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, r, s, q], [2, 1, [2, rootrp]], [3, 1, [3, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (s - 1) mod r = 0 then
        Add(all, [ [p, r, s, q], [3, 1, [3, rootsp]], [3, 2, [3, rootsr]] ]);
      fi;
      ##class 3: |Z(G)| = r, |H| = pqs, Z(H) = 1, G \cong H \times Z(G)
      if (s - 1) mod p = 0 and (q - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, s, r], [2, 1, [2, rootqp]], [3, 1, [3, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (s - 1) mod q = 0 then
        Add(all, [ [p, q, s, r], [3, 1, [3, rootsp]], [3, 2, [3, rootsq]] ]);
      fi;
      ##class 4: |Z(G)| = s, |H| = pqr, Z(H) = 1, G \cong H \times Z(G)
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [3, 1, [3, Int(v^(k*(r - 1)/p))]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]] ]);
      fi;
      data := all[i - 1 - c1];
      return SOTRec.groupFromData(data);

    ##Cluster 4: Z(G) = 1
    elif i > 1 + c1 + c2 and i < 2 + c1 + c2 + c3 then
      all := [];
      ##class 1: G' \cong C_{qrs}, G \cong C_p \ltimes C_{qrs}
      if (q - 1) mod p = 0 and (r - 1) mod p = 0 and (s - 1) mod p = 0 then
        for k in [1..(p - 1)] do
          for l in [1..(p - 1)] do
            Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^(l*(s - 1)/p))]] ]);
          od;
        od;
      fi;

      ##class 2: G' \cong C_{rs}, G \cong C_{pq} \ltimes C_{rs}
      if (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          for l in [1..(q - 1)] do
            Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 1, [4, Int(w^(k*(s - 1)/p))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
          od;
        od;
      fi;
      if (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 then
        for l in [1..(q - 1)] do
          Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^(l*(r - 1)/q))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]] ]);
        od;
      fi;
      if (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 1, [4, Int(w^(k*(s - 1)/p))]] ]);
        od;
      fi;
      if (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 then
        for l in [1..(q - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [3, 2, [3, rootrq]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (s - 1) mod q = 0 then
        Add(all, [ [p, q, r, s], [3, 1, [3, rootrp]], [4, 2, [4, rootsq]] ]);
      fi;
      if (r - 1) mod q = 0 and (s - 1) mod p = 0 then
        Add(all, [ [p, q, r, s], [3, 2, [3, rootrq]], [4, 1, [4, rootsp]] ]);
      fi;

      ##class 3: G' \cong C_{qs}, G \cong C_{pr} \ltimes C_{qs}
      if (s - 1) mod r = 0 and (q - 1) mod p = 0 then
        Add(all, [ [p, r, q, s], [3, 1, [3, rootqp]], [4, 2, [4, rootsr]] ]);
      fi;
      if (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
        for k in [1..(p - 1)] do
          Add(all, [ [p, r, q, s], [3, 1, [3, Int(u^(k*(q - 1)/p))]], [4, 1, [4, rootsp]], [4, 2, [4, rootsr]] ]);
        od;
      fi;

      ##class 4: G' \cong C_s, G \cong C_{pqr} \ltimes C_s
      if (s - 1) mod (p*q*r) = 0 then
        Add(all, [ [p, q, r, s], [4, 1, [4, rootsp]], [4, 2, [4, rootsq]], [4, 3, [4, rootsr]] ]);
      fi;
      data := all[i - 1 - c1 - c2];
      return SOTRec.groupFromData(data);
    fi;
end;
######################################################
