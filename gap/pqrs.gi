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
    m := 1 + msg.deltaDivisibility((s - 1), p*q*r)
    + msg.deltaDivisibility((r - 1), p*q) + msg.deltaDivisibility((s - 1), p*q)
    + (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), p*q)*msg.deltaDivisibility((r - 1), p*q)
    + (p - 1)*(msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), p*q) + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p*q))
    + (q - 1)*(msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), p*q) + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p*q))
    + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q) + msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p)
    + msg.deltaDivisibility((s - 1), p*r) + msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), r)
    + (p - 1)*msg.deltaDivisibility((s - 1), p*r)*msg.deltaDivisibility((q - 1), p)
    + msg.deltaDivisibility((s - 1), q*r)
    + msg.deltaDivisibility((q - 1), p)*(1 + (p - 1)*msg.deltaDivisibility((r - 1), p))
    + msg.deltaDivisibility((s - 1), p)*(1 + (p - 1)*msg.deltaDivisibility((q - 1), p))
    + msg.deltaDivisibility((r - 1), p)*(1 + (p - 1)*msg.deltaDivisibility((s - 1), p))
    + (p - 1)^2 * msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
    + msg.deltaDivisibility((s - 1), q) +  + msg.deltaDivisibility((r - 1), q) + (q - 1) * msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), q)
    + msg.deltaDivisibility((s - 1), r);

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
		c1 := msg.deltaDivisibility((s - 1), (p*q*r));
		c2 := msg.deltaDivisibility((r - 1), (p*q))
		+ msg.deltaDivisibility((s - 1), (p*q))
		+ (p - 1)*(q - 1)*msg.deltaDivisibility((s - 1), (p*q))*msg.deltaDivisibility((r - 1), (p*q))
		+ (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), (p*q))
		+ (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), (p*q))
		+ (p - 1)*msg.deltaDivisibility((s - 1), p)*msg.deltaDivisibility((r - 1), (p*q))
		+ (q - 1)*msg.deltaDivisibility((s - 1), q)*msg.deltaDivisibility((r - 1), (p*q))
		+ msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), q)
		+ msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), p);
		c3 := msg.deltaDivisibility((s - 1), p*r)
		+ msg.deltaDivisibility((s - 1), r)*msg.deltaDivisibility((q - 1), p)
		+ (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), (p*r));
		c4 := msg.deltaDivisibility((s - 1), (q*r));
		c5 := msg.deltaDivisibility((q - 1), p)
		+ msg.deltaDivisibility((r - 1), p)
		+ msg.deltaDivisibility((s - 1), p)
		+ (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)
		+ (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((s - 1), p)
		+ (p - 1)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p)
		+ (p - 1)^2*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((s - 1), p);
		c6 := msg.deltaDivisibility((r - 1), q)
		+ msg.deltaDivisibility((s - 1), q)
		+ (q - 1)*msg.deltaDivisibility((r - 1), q)*msg.deltaDivisibility((s - 1), q);
		c7 := msg.deltaDivisibility((s - 1), r);

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

msg.totestpqrs := function(from, to)
  local list, p, q, r, s;
    list := [];
    for p in Filtered([from..to], x -> IsPrimeInt(x) = true) do
      for q in Filtered([p + 1..to], x -> x > p and IsPrimeInt(x) = true) do
        for r in Filtered([q + 1..to], x -> x > q and IsPrimeInt(x) = true) do
          for s in Filtered([r + 1..to], x -> x > r and IsPrimeInt(x) = true) do
            if (q - 1) mod p = 0 or (r - 1) mod p = 0 or (s - 1) mod p = 0
              or (r - 1) mod q = 0 or (s - 1) mod q = 0
              or (s - 1) mod q = 0 then
                Add(list, [p, q, r, s]);
            fi;
          od;
        od;
      od;
    od;
  return list;
end;
