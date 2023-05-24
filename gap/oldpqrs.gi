## Construction of squarefree groups of order pqrs.
## The classification of these groups follows from the following theorem by Hoelder, Burnside, and Zassenhaus:
## Let G be a group of order n whose Sylow subgroups are cyclic. Then G is metacyclic with odd-order derived subgroup [G, G] \cong C_b and cyclic quotient G/[G, G] \cong C_a, where a = n/b.
## In particular, G is isomorphic to <x, y | x^a, y^b, y^x = y^r > for some non-negative integer r such that r^a = 1 mod b, and gcd(a(r - 1), b) = 1.
## Alternatively, one can use the fact that G is solvable and has a nontrivial, abelian Fitting subgroup, denoted by F, to construct and classify the isomorphism types of G as an extension of F by G/F.
  #Note that G/F embeds into Aut(F).
## To use the construction by case distinction on the size of F (the Fitting subgroup of G), set USE_pqrsII := false; otherwise, the main construction functions AllSOTGroups and SOTGroup use the case distinction by the centre and the derived subgroup of G, with USE_pqrsII = true.

##############################################
SOTRec.allGroupsPQRS := function(n)
  local all, fac, p, q, r, s, u, v, w, k, l, list;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
    all := [ [ [p, q, r, s] ] ];
    u := Z(q);
    v := Z(r);
    w := Z(s);
    ### case 1: |F| = s, pqr | (s - 1), and G \cong C_{pqr} \ltimes C_s
    if (s - 1) mod (p*q*r) = 0 then
      Add(all, [ [p, q, r, s], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]], [4, 3, [4, Int(w^((s - 1)/r))]] ]);
    fi;

    ### case 2: |F| = rs, pq | (r - 1)(s - 1), and G \cong C_{pq} \ltimes C_{rs}
    if (r - 1) mod (p*q) = 0 then
      Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]] ]);
    fi;
    if (s - 1) mod (p*q) = 0 then
      Add(all, [ [p, q, r, s], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
    fi;
    if (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 then
      for k in [1..(p - 1)] do
        for l in [1..(q - 1)] do
          Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^(k*(s - 1)/p))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
        od;
      od;
    fi;
    if (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 then
      for l in [1..(q - 1)] do
        Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^(l*(r - 1)/q))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
      od;
    fi;
    if (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^(k*(s - 1)/p))]] ]);
      od;
    fi;
    if (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 then
      for l in [1..(q - 1)] do
        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod p = 0 and (s - 1) mod q = 0 then
      Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (s - 1) mod p = 0 then
      Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^((s - 1)/p))]] ]);
    fi;

    ### case 3: |F| = qs, r |(s - 1), p | (q - 1)(s - 1), and G \cong C_{pr} \ltimes C_{qs}
    if (s - 1) mod (p*r) = 0 then
      Add(all, [ [p, r, s, q], [3, 1, [3, Int(w^((s - 1)/p))]], [3, 2, [3, Int(w^((s - 1)/r))]] ]);
    fi;
    if (s - 1) mod r = 0 and (q - 1) mod p = 0 then
      Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]], [4, 3, [4, Int(w^((s - 1)/r))]] ]);
    fi;
    if (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, r, q, s], [3, 1, [3, Int(u^(k*(q - 1)/p))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/r))]] ]);
      od;
    fi;

    ###case 4: |F| = ps, qr | (s - 1) and G \cong (C_{qr} \ltimes C_s) \times C_p
    if (s - 1) mod (q*r) = 0 then
      Add(all, [ [q, r, s, p], [3, 1, [3, Int(w^((s - 1)/q))]], [3, 2, [3, Int(w^((s - 1)/r))]] ]);
    fi;

    ###case 5: |F| = qrs, p | (q - 1)(r - 1)(s - 1), and G \cong C_p \ltimes C_{qrs}
    if (q - 1) mod p = 0 then
      Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]] ]);
    fi;
    if (r - 1) mod p = 0 then
      Add(all, [ [p, r, q, s], [2, 1, [2, Int(v^((r - 1)/p))]] ]);
    fi;
    if (s - 1) mod p = 0 then
      Add(all, [ [p, s, q, r], [2, 1, [2, Int(w^((s - 1)/p))]] ]);
    fi;
    if (q - 1) mod p = 0 and (r - 1) mod p = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^(k*(q - 1)/p))]], [3, 1, [3, Int(v^((r - 1)/p))]] ]);
      od;
    fi;
    if (q - 1) mod p = 0 and (s - 1) mod p = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, q, s, r], [2, 1, [2, Int(u^(k*(q - 1)/p))]], [3, 1, [3, Int(w^((s - 1)/p))]] ]);
      od;
    fi;
    if (r - 1) mod p = 0 and (s - 1) mod p = 0 then
      for k in [1..(p - 1)] do
        Add(all, [ [p, r, s, q], [2, 1, [2, Int(v^(k*(r - 1)/p))]], [3, 1, [3, Int(w^((s - 1)/p))]] ]);
      od;
    fi;
    if (q - 1) mod p = 0 and (r - 1) mod p = 0 and (s - 1) mod p = 0 then
      for k in [1..(p - 1)] do
        for l in [1..(p - 1)] do
          Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^(l*(s - 1)/p))]] ]);
        od;
      od;
    fi;

    ###case 6: |F| = prs, q | (r - 1)(s - 1), and G \cong (C_q \ltimes C_{rs}) \times C_p
    if (r - 1) mod q = 0 then
      Add(all, [ [q, r, s, p], [2, 1, [2, Int(v^((r - 1)/q))]] ]);
    fi;
    if (s - 1) mod q = 0 then
      Add(all, [ [q, r, s, p], [3, 1, [3, Int(w^((s - 1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (s - 1) mod q = 0 then
      for k in [1..(q - 1)] do
        Add(all, [ [q, r, s, p], [2, 1, [2, Int(v^((r - 1)/q))]], [3, 1, [3, Int(w^(k*(s - 1)/q))]] ]);
      od;
    fi;

    ###case7: |F| = pqs, r | (s - 1), and G \cong (C_r \ltimes C_s) \times C_p \times C_q
    if (s - 1) mod r = 0 then
      Add(all, [ [r, s, p, q], [2, 1, [2, Int(w^((s - 1)/r))]] ]);
    fi;

    list := List(all, x -> SOTRec.groupFromData(x));
  return list;
end;

######################################################
SOTRec.NumberGroupsPQRS := function(n)
  local fac, p, q, r, s, m;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
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
SOTRec.GroupPQRS := function(n, i)
  local all, fac, p, q, r, s, u, v, w, k, l, G,
	c1, c2, c3, c4, c5, c6, c7, data;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
    all := [ [ [p, q, r, s] ] ];
    u := Z(q);
    v := Z(r);
    w := Z(s);
    ### enumeration
		c1 := SOTRec.w((s - 1), (p*q*r));
		c2 := SOTRec.w((r - 1), (p*q))
		+ SOTRec.w((s - 1), (p*q))
		+ (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
		+ (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
		+ (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
		+ (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
		+ (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
		+ SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
		+ SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p);
		c3 := SOTRec.w((s - 1), p*r)
		+ SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
		+ (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), (p*r));
		c4 := SOTRec.w((s - 1), (q*r));
		c5 := SOTRec.w((q - 1), p)
		+ SOTRec.w((r - 1), p)
		+ SOTRec.w((s - 1), p)
		+ (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)
		+ (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
		+ (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
		+ (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p);
		c6 := SOTRec.w((r - 1), q)
		+ SOTRec.w((s - 1), q)
		+ (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q);
		c7 := SOTRec.w((s - 1), r);

    if i = 1 then return SOTRec.groupFromData(all[1]); fi;
    ### case 1: |F| = s, pqr | (s - 1), and G \cong C_{pqr} \ltimes C_s
    if (s - 1) mod (p*q*r) = 0 and i > 1 and i < 2 + c1 then
      return SOTRec.groupFromData([ [p, q, r, s], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]], [4, 3, [4, Int(w^((s - 1)/r))]] ]);
    fi;

    ### case 2: |F| = rs, pq | (r - 1)(s - 1), and G \cong C_{pq} \ltimes C_{rs}
		if (r - 1)*(s - 1) mod (p*q) = 0 and i > 1 + c1 and i < 2 + c1 + c2 then
			all := [];
	    if (r - 1) mod (p*q) = 0 then
	      Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]] ]);
	    fi;
	    if (s - 1) mod (p*q) = 0 then
	      Add(all, [ [p, q, r, s], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
	    fi;
	    if (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 then
	      for k in [1..(p - 1)] do
	        for l in [1..(q - 1)] do
	          Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^(k*(s - 1)/p))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
	        od;
	      od;
	    fi;
	    if (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
	      od;
	    fi;
	    if (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 then
	      for l in [1..(q - 1)] do
	        Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^(l*(r - 1)/q))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
	      od;
	    fi;
	    if (s - 1) mod p = 0 and (r - 1) mod (p*q) = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^(k*(s - 1)/p))]] ]);
	      od;
	    fi;
	    if (s - 1) mod q = 0 and (r - 1) mod (p*q) = 0 then
	      for l in [1..(q - 1)] do
	        Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 2, [4, Int(w^(l*(s - 1)/q))]] ]);
	      od;
	    fi;
	    if (r - 1) mod p = 0 and (s - 1) mod q = 0 then
	      Add(all, [ [p, q, r, s], [3, 1, [3, Int(v^((r - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]] ]);
	    fi;
	    if (r - 1) mod q = 0 and (s - 1) mod p = 0 then
	      Add(all, [ [p, q, r, s], [3, 2, [3, Int(v^((r - 1)/q))]], [4, 1, [4, Int(w^((s - 1)/p))]] ]);
	    fi;
			data := all[i - 1 - c1];
			return SOTRec.groupFromData(data);
		fi;

    ### case 3: |F| = qs, r |(s - 1), p | (q - 1)(s - 1), and G \cong C_{pr} \ltimes C_{qs}
		if (s - 1) mod r = 0 and (q - 1)*(s - 1) mod p = 0 and i > 1 + c1 + c2 and i < 2 + c1 + c2 + c3 then
			all := [];
	    if (s - 1) mod (p*r) = 0 then
	      Add(all, [ [p, r, s, q], [3, 1, [3, Int(w^((s - 1)/p))]], [3, 2, [3, Int(w^((s - 1)/r))]] ]);
	    fi;
	    if (s - 1) mod r = 0 and (q - 1) mod p = 0 then
	      Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]], [4, 3, [4, Int(w^((s - 1)/r))]] ]);
	    fi;
	    if (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, r, q, s], [3, 1, [3, Int(u^(k*(q - 1)/p))]], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/r))]] ]);
	      od;
	    fi;
			data := all[i - 1 - c1 - c2];
			return SOTRec.groupFromData(data);
		fi;

    ###case 4: |F| = ps, qr | (s - 1) and G \cong (C_{qr} \ltimes C_s) \times C_p
		if (s - 1) mod (q*r) = 0 and i > 1 + c1 + c2 + c3 and i < 2 + c1 + c2 + c3 + c4 then
			return SOTRec.groupFromData([ [q, r, s, p], [3, 1, [3, Int(w^((s - 1)/q))]], [3, 2, [3, Int(w^((s - 1)/r))]] ]);
		fi;

    ###case 5: |F| = qrs, p | (q - 1)(r - 1)(s - 1), and G \cong C_p \ltimes C_{qrs}
		if (q - 1)*(r - 1)*(s - 1) mod p = 0 and i > 1 + c1 + c2 + c3 + c4 and i < 2 + c1 + c2 + c3 + c4 + c5 then
			all := [];
	    if (q - 1) mod p = 0 then
	      Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]] ]);
	    fi;
	    if (r - 1) mod p = 0 then
	      Add(all, [ [p, r, q, s], [2, 1, [2, Int(v^((r - 1)/p))]] ]);
	    fi;
	    if (s - 1) mod p = 0 then
	      Add(all, [ [p, s, q, r], [2, 1, [2, Int(w^((s - 1)/p))]] ]);
	    fi;
	    if (q - 1) mod p = 0 and (r - 1) mod p = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^(k*(q - 1)/p))]], [3, 1, [3, Int(v^((r - 1)/p))]] ]);
	      od;
	    fi;
	    if (q - 1) mod p = 0 and (s - 1) mod p = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, q, s, r], [2, 1, [2, Int(u^(k*(q - 1)/p))]], [3, 1, [3, Int(w^((s - 1)/p))]] ]);
	      od;
	    fi;
	    if (r - 1) mod p = 0 and (s - 1) mod p = 0 then
	      for k in [1..(p - 1)] do
	        Add(all, [ [p, r, s, q], [2, 1, [2, Int(v^(k*(r - 1)/p))]], [3, 1, [3, Int(w^((s - 1)/p))]] ]);
	      od;
	    fi;
	    if (q - 1) mod p = 0 and (r - 1) mod p = 0 and (s - 1) mod p = 0 then
	      for k in [1..(p - 1)] do
	        for l in [1..(p - 1)] do
	          Add(all, [ [p, q, r, s], [2, 1, [2, Int(u^((q - 1)/p))]], [3, 1, [3, Int(v^(k*(r - 1)/p))]], [4, 1, [4, Int(w^(l*(s - 1)/p))]] ]);
	        od;
	      od;
	    fi;
			data := all[i - 1 - c1 - c2 - c3 - c4];
			return SOTRec.groupFromData(data);
		fi;

    ###case 6: |F| = prs, q | (r - 1)(s - 1), and G \cong (C_q \ltimes C_{rs}) \times C_p
		if (r - 1)*(s - 1) mod q = 0 and i > 1 + c1 + c2 + c3 + c4 + c5 and i < 2 + c1 + c2 + c3 + c4 + c5 + c6 then
			all := [];
	    if (r - 1) mod q = 0 then
	      Add(all, [ [q, r, s, p], [2, 1, [2, Int(v^((r - 1)/q))]] ]);
	    fi;
	    if (s - 1) mod q = 0 then
	      Add(all, [ [q, r, s, p], [3, 1, [3, Int(w^((s - 1)/q))]] ]);
	    fi;
	    if (r - 1) mod q = 0 and (s - 1) mod q = 0 then
	      for k in [1..(q - 1)] do
	        Add(all, [ [q, r, s, p], [2, 1, [2, Int(v^((r - 1)/q))]], [3, 1, [3, Int(w^(k*(s - 1)/q))]] ]);
	      od;
	    fi;
			data := all[i - 1 - c1 - c2 - c3 - c4 - c5];
			return SOTRec.groupFromData(data);
		fi;

    ###case7: |F| = pqs, r | (s - 1), and G \cong (C_r \ltimes C_s) \times C_p \times C_q
    if (s - 1) mod r = 0 then
      return SOTRec.groupFromData([ [r, s, p, q], [2, 1, [2, Int(w^((s - 1)/r))]] ]);
    fi;
end;
######################################################
SOTRec.allGroupsPQRSII := function(n)
  local all, fac, p, q, r, s, u, v, w, k, l, rootsr, rootsq, rootsp, rootrq, rootrp, rootqp, tmp, listall;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
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
        Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [4, 3, [4, rootsr]] ]);
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
SOTRec.GroupPQRSII := function(n, i)
  local all, fac, p, q, r, s, u, v, w, j, k, l, c1, c2, c3, rootsr, rootsq, rootsp, rootrq, rootrp, rootqp, tmp, data;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
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

    if i = 1 then return SOTRec.groupFromData(all[1]);
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
        Add(all, [ [p, q, r, s], [2, 1, [2, rootqp]], [4, 3, [4, rootsr]] ]);
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
SOTRec.infoPQRS := function(n)
  local c, sot, fac, p, q, r, s, m;
    sot := SOTRec.sot(n);
    c := [];
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 4 then
      Error("Argument must be of the form of pqrs");
    else
      p := fac[1];
      q := fac[2];
      r := fac[3];
      s := fac[4];
    fi;
    ##Cluster 1: Abelian group, Z(G) = G
    ##enumeration of each case by size of the centre
    c[1] := SOTRec.w((s - 1), r) + SOTRec.w((s - 1), q) + SOTRec.w((r - 1), q)
        + SOTRec.w((s - 1), p) + SOTRec.w((r - 1), p) + SOTRec.w((q - 1), p);
    c[2] := (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q) + SOTRec.w((s - 1), (q*r))
        + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*r))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p) + SOTRec.w((s - 1), (p*q))
        + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p) + SOTRec.w((r - 1), (p*q));
    c[3] := (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
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
    m := Sum(c);
    if m = 0 then
      Print("\n  There is 1 group of order ", n,".\n");
      Print("\n  All groups of order ", n, " are abelian.\n");
    else
      Print("\n  There are ", m + 1, " groups of order ", n,".\n");
      Print("\n  The groups of order pqrs are solvable and classified by H\"older.\n");
      Print("  These groups are sorted by their centre. \n");
      Print(sot, "1 is abelian.\n");
      if c[1] = 1 then
        Print(sot, 1+c[1]," has centre of order that is a product of two distinct primes.\n");
      elif c[1] > 1 then
        Print(sot, "2 - ", 1+c[1], " have centre of order that is a product of two distinct primes.\n");
      fi;
      if c[2] = 1 then
        Print(sot, 1+c[1]+c[2]," has a cyclic centre of prime order.\n");
      elif c[2] > 1 then
        Print(sot, 2 + c[1], " - ", 1+c[1]+c[2], " have a cyclic centre of prime order.\n");
      fi;
      if c[3] = 1 then
        Print(sot, 1+m," has trivial centre.\n");
      elif c[2] > 1 then
        Print(sot, 2 + c[1]+c[2], " - ", 1+m, " have a trivial centre.\n");
      fi;
    fi;
    Print("\n");
  end;

  #
  # the case of groups of order pqrs
  #
  SOTRec.IdGroupPQRS := function(group)
    local n, fac, p, q, r, s, P, Q, R, S, H, u, v, w, k, l, flag, lst, sizefit,
    G, pcgs, pc, fgens, i, a, b, c, d, x, y, Id,
    c1, c2, c3, c4, c5, c6, exprp, exprq, expsp, expsq, expsr, expqp,
    pcgsp, pcgsq, pcgsr, pcgss;
      n := Order(group);
      fac := Factors(n);
      if not List(Collected(fac), x->x[2]) = [1, 1, 1, 1] then
        Error("Argument must be of the form of pqrs");
      else
        p := fac[1];
        q := fac[2];
        r := fac[3];
        s := fac[4];
      fi;

      P := SylowSubgroup(group, p);
      Q := SylowSubgroup(group, q);
      R := SylowSubgroup(group, r);
      S := SylowSubgroup(group, s);
      pcgsp := Pcgs(P);
      pcgsq := Pcgs(Q);
      pcgsr := Pcgs(R);
      pcgss := Pcgs(S);

      u := Z(q);
      v := Z(r);
      w := Z(s);

      if IsAbelian(group) then return [n, 1];
      else
        flag := [Size(FittingSubgroup(group)), Size(Centre(group))];
        pcgs := [pcgsp[1], pcgsq[1], pcgsr[1], pcgss[1]];
        pc := PcgsByPcSequence(FamilyObj(pcgs[1]), pcgs);
        exprp := ExponentsOfPcElement(pc, pcgs[3]^pcgs[1]);
        exprq := ExponentsOfPcElement(pc, pcgs[3]^pcgs[2]);
        expsp := ExponentsOfPcElement(pc, pcgs[4]^pcgs[1]);
        expsq := ExponentsOfPcElement(pc, pcgs[4]^pcgs[2]);
        expsr := ExponentsOfPcElement(pc, pcgs[4]^pcgs[3]);
        expqp := ExponentsOfPcElement(pc, pcgs[2]^pcgs[1]);
      fi;

      c1 := SOTRec.w((s - 1), (p*q*r));
      c2 := SOTRec.w((r - 1), (p*q))
      + SOTRec.w((s - 1), (p*q))
      + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
      + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
      + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
      + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
      + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
      + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q)
      + SOTRec.w((r - 1), q)*SOTRec.w((s - 1), p);
      c3 := SOTRec.w((s - 1), p*r)
      + SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
      + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), (p*r));
      c4 := SOTRec.w((s - 1), (q*r));
      c5 := SOTRec.w((q - 1), p)
      + SOTRec.w((r - 1), p)
      + SOTRec.w((s - 1), p)
      + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)
      + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
      + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
      + (p - 1)^2*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p);
      c6 := SOTRec.w((r - 1), q)
      + SOTRec.w((s - 1), q)
      + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), q);
      if flag[1] = s and (s - 1) mod (p*q*r) = 0 then
        return [n, 2];
      fi;
      if flag[1] = r * s and (r - 1)*(s - 1) mod (p*q) = 0 then
        if flag[2] = s then return [n, 2 + c1];
        elif flag[2] = r then
          return [n, 2 + c1
          + SOTRec.w((r - 1), (p*q))];
        elif (s - 1) mod (p*q) = 0 and (r - 1) mod (p*q) = 0 and
          exprp[3] <> 1 and
          exprq[3] <> 1 and
          expsp[4] <> 1 and
          expsq[4] <> 1 then
          x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
          y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
          l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
          return [n, 2 + c1
          + SOTRec.w((r - 1), (p*q))
          + SOTRec.w((s - 1), (p*q))
          + l + (k - 1)*(q - 1) - 1 ];
        elif (r - 1) mod p = 0 and (s - 1) mod (p*q) = 0 and exprq[3] = 1 then
          if expsp[4] <> 1 and expsq[4] <> 1 then
            x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
            k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + k - 1 ];
          elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and expsp[4] = 1 then
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q)) ];
          fi;
        elif (r - 1) mod q = 0 and (s - 1) mod (p*q) = 0 and exprp[3] = 1 then
          if expsp[4] <> 1 and expsq[4] <> 1 then
            y := Inverse(LogFFE(expsq[4]*One(GF(s)), w^((s - 1)/q))) mod q;
            l := LogFFE(exprq[3]^y*One(GF(r)), v^((r - 1)/q)) mod q;
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + l - 1 ];
          elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and expsq[4] = 1 then
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
            + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q) ];
          fi;
        elif expsq[4] = 1 then
          if exprp[3] <> 1 and exprq[3]<> 1 then
            x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
            k := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + k - 1 ];
          elif (r - 1) mod q = 0 and (s - 1) mod p = 0 and expsq[4] = 1 then
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q))
            + SOTRec.w((r - 1), p)*SOTRec.w((s - 1), q) ];
            fi;
        elif expsp[4] = 1 then
          if exprp[3] <> 1 and exprq[3] <> 1 then
            y := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
            l := LogFFE(expsq[4]^y*One(GF(s)), w^((s - 1)/q)) mod q;
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + l - 1 ];
          elif (r - 1) mod p = 0 and (s - 1) mod q = 0 and exprq[3] = 1 then
            return [n, 2 + c1
            + SOTRec.w((r - 1), (p*q))
            + SOTRec.w((s - 1), (p*q))
            + (p - 1)*(q - 1)*SOTRec.w((s - 1), (p*q))*SOTRec.w((r - 1), (p*q))
            + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), (p*q))
            + (q - 1)*SOTRec.w((r - 1), q)*SOTRec.w((s - 1), (p*q))
            + (p - 1)*SOTRec.w((s - 1), p)*SOTRec.w((r - 1), (p*q))
            + (q - 1)*SOTRec.w((s - 1), q)*SOTRec.w((r - 1), (p*q)) ];
          fi;
        fi;
      fi;
      if flag[1] = q * s then
        if flag[2] = q then
          return [n, 2 + c1 + c2];
        elif (s - 1) mod r = 0 and (q - 1) mod p = 0 and expsp[4] = 1 then
          return [n, 2 + c1 + c2
          + SOTRec.w((s - 1), p*r)];
        elif (q - 1) mod p = 0 and (s - 1) mod (p*r) = 0 then
          if expsp[4] <> 1 and expsr[4] <> 1 then
            x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
            k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
            return [n, 2 + c1 + c2
            + SOTRec.w((s - 1), p*r)
            + SOTRec.w((s - 1), r)*SOTRec.w((q - 1), p)
            + k - 1 ];
          fi;
        fi;
      fi;
      if flag[1] = p * s then
        return [n, 2 + c1 + c2 + c3];
      fi;
      if flag[1] = q * r * s then
        if flag[2] = r * s then
          return [n, 2 + c1 + c2 + c3 + c4];
        elif flag[2] = q * s then
          return [n, 2 +  c1 + c2 + c3 + c4
          + SOTRec.w((q - 1), p) ];
        elif flag[2] = q * r then
          return [n, 2 + c1 + c2 + c3 + c4
          + SOTRec.w((q - 1), p)
          + SOTRec.w((r - 1), p)];
        elif flag[2] = s then
          if exprp[3] <> 1 then
            x := Inverse(LogFFE(exprp[3]*One(GF(r)), v^((r - 1)/p))) mod p;
            k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
            return [n, 2 + c1 + c2 + c3 + c4
            + SOTRec.w((q - 1), p)
            + SOTRec.w((r - 1), p)
            + SOTRec.w((s - 1), p)
            + k - 1 ];
          fi;
        elif flag[2] = r then
          if expsp[4] <> 1 then
            x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
            k := LogFFE(expqp[2]^x*One(GF(q)), u^((q - 1)/p)) mod p;
            return [n, 2 + c1 + c2 + c3 + c4
            + SOTRec.w((q - 1), p)
            + SOTRec.w((r - 1), p)
            + SOTRec.w((s - 1), p)
            + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)
            + k - 1 ];
          fi;
        elif flag[2] = q then
          if expsp[4] <> 1 then
            x := Inverse(LogFFE(expsp[4]*One(GF(s)), w^((s - 1)/p))) mod p;
            k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
            return [n, 2 + c1 + c2 + c3 + c4
            + SOTRec.w((q - 1), p)
            + SOTRec.w((r - 1), p)
            + SOTRec.w((s - 1), p)
            + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)
            + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
            + k - 1 ];
          fi;
        elif expqp[2] <> 1 then
          x := Inverse(LogFFE(expqp[2]*One(GF(q)), u^((q - 1)/p))) mod p;
          k := LogFFE(exprp[3]^x*One(GF(r)), v^((r - 1)/p)) mod p;
          l := LogFFE(expsp[4]^x*One(GF(s)), w^((s - 1)/p)) mod p;
          return [n, 2 + c1 + c2 + c3 + c4
          + SOTRec.w((q - 1), p)
          + SOTRec.w((r - 1), p)
          + SOTRec.w((s - 1), p)
          + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p)
          + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((s - 1), p)
          + (p - 1)*SOTRec.w((r - 1), p)*SOTRec.w((s - 1), p)
          + l + (k - 1)*(p - 1) - 1 ];
        fi;
      fi;
      if flag[1] = p * r * s then
        if expsq[4] = 1 and exprq[3] <> 1 then
          return [n, 2 + c1 + c2 + c3 + c4 + c5];
        elif expsq[4] <> 1 and exprq[3] = 1 then
          return [n, 2 + c1 + c2 + c3 + c4 + c5
          + SOTRec.w((r - 1), q) ];
        elif exprq[3] <> 1 then
          x := Inverse(LogFFE(exprq[3]*One(GF(r)), v^((r - 1)/q))) mod q;
          k := LogFFE(expsq[4]^x*One(GF(s)), w^((s - 1)/q)) mod q;
          return [n, 2 + c1 + c2 + c3 + c4 + c5
          + SOTRec.w((r - 1), q)
          + SOTRec.w((s - 1), q)
          + k - 1 ];
        fi;
      fi;
      if flag[1] = p * q * s then
        return [n, 2 + c1 + c2 + c3 + c4 + c5 + c6];
      fi;
  end;