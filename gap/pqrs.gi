## Construction of squarefree groups of order pqr.
## The classification of these groups follows from the following theorem by Hoelder, Burnside, and Zassenhaus:
## Let G be a group of order n whose Sylow subgroups are cyclic. Then G is metacyclic with odd-order derived subgroup [G, G] \cong C_b and cyclic quotient G/[G, G] \cong C_a, where a = n/b.
## In particular, G is isomorphic to <x, y | x^a, y^b, y^x = y^r > for some non-negative integer r such that r^a = 1 mod b, and gcd(a(r - 1), b) = 1.
## Alternatively, one can use the fact that G is solvable and has a nontrivial, abelian Fitting subgroup, denoted by F, to construct and classify the isomorphism types of G as an extension of F by G/F.
  #Note that G/F embeds into Aut(F).

##############################################
msg.allGroupsPQRS := function(n)
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

    list := List(all, x -> msg.groupFromData(x));
  return list;
end;

######################################################
msg.NumberGroupsPQRS := function(n)
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
    m := 1 + msg.w((s - 1), p*q*r)
    + msg.w((r - 1), p*q) + msg.w((s - 1), p*q)
    + (p - 1)*(q - 1)*msg.w((s - 1), p*q)*msg.w((r - 1), p*q)
    + (p - 1)*(msg.w((s - 1), p)*msg.w((r - 1), p*q) + msg.w((r - 1), p)*msg.w((s - 1), p*q))
    + (q - 1)*(msg.w((s - 1), q)*msg.w((r - 1), p*q) + msg.w((r - 1), q)*msg.w((s - 1), p*q))
    + msg.w((r - 1), p)*msg.w((s - 1), q) + msg.w((r - 1), q)*msg.w((s - 1), p)
    + msg.w((s - 1), p*r) + msg.w((q - 1), p)*msg.w((s - 1), r)
    + (p - 1)*msg.w((s - 1), p*r)*msg.w((q - 1), p)
    + msg.w((s - 1), q*r)
    + msg.w((q - 1), p)*(1 + (p - 1)*msg.w((r - 1), p))
    + msg.w((s - 1), p)*(1 + (p - 1)*msg.w((q - 1), p))
    + msg.w((r - 1), p)*(1 + (p - 1)*msg.w((s - 1), p))
    + (p - 1)^2 * msg.w((q - 1), p)*msg.w((r - 1), p)*msg.w((s - 1), p)
    + msg.w((s - 1), q) + msg.w((r - 1), q) + (q - 1) * msg.w((r - 1), q)*msg.w((s - 1), q)
    + msg.w((s - 1), r);

  return m;
end;
######################################################
msg.GroupPQRS := function(n, i)
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
		c1 := msg.w((s - 1), (p*q*r));
		c2 := msg.w((r - 1), (p*q))
		+ msg.w((s - 1), (p*q))
		+ (p - 1)*(q - 1)*msg.w((s - 1), (p*q))*msg.w((r - 1), (p*q))
		+ (p - 1)*msg.w((r - 1), p)*msg.w((s - 1), (p*q))
		+ (q - 1)*msg.w((r - 1), q)*msg.w((s - 1), (p*q))
		+ (p - 1)*msg.w((s - 1), p)*msg.w((r - 1), (p*q))
		+ (q - 1)*msg.w((s - 1), q)*msg.w((r - 1), (p*q))
		+ msg.w((r - 1), p)*msg.w((s - 1), q)
		+ msg.w((r - 1), q)*msg.w((s - 1), p);
		c3 := msg.w((s - 1), p*r)
		+ msg.w((s - 1), r)*msg.w((q - 1), p)
		+ (p - 1)*msg.w((q - 1), p)*msg.w((s - 1), (p*r));
		c4 := msg.w((s - 1), (q*r));
		c5 := msg.w((q - 1), p)
		+ msg.w((r - 1), p)
		+ msg.w((s - 1), p)
		+ (p - 1)*msg.w((q - 1), p)*msg.w((r - 1), p)
		+ (p - 1)*msg.w((q - 1), p)*msg.w((s - 1), p)
		+ (p - 1)*msg.w((r - 1), p)*msg.w((s - 1), p)
		+ (p - 1)^2*msg.w((q - 1), p)*msg.w((r - 1), p)*msg.w((s - 1), p);
		c6 := msg.w((r - 1), q)
		+ msg.w((s - 1), q)
		+ (q - 1)*msg.w((r - 1), q)*msg.w((s - 1), q);
		c7 := msg.w((s - 1), r);

    if i = 1 then return msg.groupFromData(all[1]); fi;
    ### case 1: |F| = s, pqr | (s - 1), and G \cong C_{pqr} \ltimes C_s
    if (s - 1) mod (p*q*r) = 0 and i > 1 and i < 2 + c1 then
      return msg.groupFromData([ [p, q, r, s], [4, 1, [4, Int(w^((s - 1)/p))]], [4, 2, [4, Int(w^((s - 1)/q))]], [4, 3, [4, Int(w^((s - 1)/r))]] ]);
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
			return msg.groupFromData(data);
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
			return msg.groupFromData(data);
		fi;

    ###case 4: |F| = ps, qr | (s - 1) and G \cong (C_{qr} \ltimes C_s) \times C_p
		if (s - 1) mod (q*r) = 0 and i > 1 + c1 + c2 + c3 and i < 2 + c1 + c2 + c3 + c4 then
			return msg.groupFromData([ [q, r, s, p], [3, 1, [3, Int(w^((s - 1)/q))]], [3, 2, [3, Int(w^((s - 1)/r))]] ]);
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
			return msg.groupFromData(data);
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
			return msg.groupFromData(data);
		fi;

    ###case7: |F| = pqs, r | (s - 1), and G \cong (C_r \ltimes C_s) \times C_p \times C_q
    if (s - 1) mod r = 0 then
      return msg.groupFromData([ [r, s, p, q], [2, 1, [2, Int(w^((s - 1)/r))]] ]);
    fi;
end;
######################################################
msg.allGroupsPQRSII := function(n)
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
    ##case 0: Abelian group, Z(G) = G
    all := [ [ [p, q, r, s] ] ];

    u := Z(q);
    v := Z(r);
    w := Z(s);

    ##case 1: |Z(G)| \in {pq, pr, ps, qr, qs, rs}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
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

    ##case 2: |Z(G)| \in {p, q, r, s}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
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

    ##case 3: Z(G) = 1
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
    listall := List(all, x -> msg.groupFromData(x));
  return listall;
end;
######################################################
msg.GroupPQRSII := function(n, i)
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
    ##case 0: Abelian group, Z(G) = G
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
    c1 := msg.w((s - 1), r) + msg.w((s - 1), q) + msg.w((r - 1), q)
        + msg.w((s - 1), p) + msg.w((r - 1), p) + msg.w((q - 1), p);
    c2 := (q - 1)*msg.w((r - 1), q)*msg.w((s - 1), q) + msg.w((s - 1), (q*r))
        + (p - 1)*msg.w((r - 1), p)*msg.w((s - 1), p) + msg.w((s - 1), (p*r))
        + (p - 1)*msg.w((q - 1), p)*msg.w((s - 1), p) + msg.w((s - 1), (p*q))
        + (p - 1)*msg.w((q - 1), p)*msg.w((r - 1), p) + msg.w((r - 1), (p*q));
    c3 := (p - 1)^2*msg.w((q - 1), p)*msg.w((r - 1), p)*msg.w((s - 1), p)
        + (p - 1)*(q - 1)*msg.w((s - 1), (p*q))*msg.w((r - 1), (p*q))
        + (p - 1)*msg.w((r - 1), p)*msg.w((s - 1), (p*q))
        + (q - 1)*msg.w((r - 1), q)*msg.w((s - 1), (p*q))
        + (p - 1)*msg.w((s - 1), p)*msg.w((r - 1), (p*q))
        + (q - 1)*msg.w((s - 1), q)*msg.w((r - 1), (p*q))
        + msg.w((r - 1), p)*msg.w((s - 1), q)
        + msg.w((r - 1), q)*msg.w((s - 1), p)
        + msg.w((s - 1), r)*msg.w((q - 1), p)
        + (p - 1)*msg.w((q - 1), p)*msg.w((s - 1), (p*r))
        + msg.w((s - 1), (p*q*r));

    if i = 1 then return msg.groupFromData(all[1]);
    ##case 1: |Z(G)| \in {pq, pr, ps, qr, qs, rs}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
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
      return msg.groupFromData(data);

    ##case 2: |Z(G)| \in {p, q, r, s}, G \cong H \times Z(G), where gcd(|H|, |Z(G)|) = 1 and Z(H) = 1
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
      return msg.groupFromData(data);

    ##case 3: Z(G) = 1
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
			return msg.groupFromData(data);
    fi;
end;
