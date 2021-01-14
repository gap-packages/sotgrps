## The following functions contribute to AllSOTGroups, NumberOfSOTGroups, and SOTGroup, respectively.

## Groups of order p^2q (p, q distinct primes) are solvable by Burnside's pq-theorem.
	## Every such group has a normal Sylow subgroup by Sylow's theorems.
## Let G be a group of order p^2q, Q \in Syl_q(G) and P \in Syl_p(G). The Q \cong C_q and P \in \{C_{p^2}, C_p^2\}.
## The nilpotent groups of such order are precisely the abelian groups, which are classifed by the fundamental theorem of finitely generated abelian groups.

## The classification of the non-nilpotent groups follows by classifying semidirect products Q \ltimes P and P \ltimes Q.
## The enumeration of these groups follows from [2, Theorem 2.1 a)].
	## See [2, Section 3.2 & 3.4] for further details.

## The following remark also applies to other order types including pq, p^3q, p^4q, etc.
	## If a non-nilpotent group of order n = p^nq has a normal Sylow subgroup, then it is isomorphic to a split extensions of the form C_q \ltimes P or P \ltimes C_q, where P is a Sylow p-subgroup of G.
	## Such split extensions are classified by [2, Proposition 3.3 & 3.6].

## Globally, we use GAP's inbuilt function Z(p) to compute \sigma_p (see [2, Notation 2.3]) for the canonical primitive root modulo p (where p is a prime), and compute \rho(p, b) accordingly for b dividing (p - 1).
	## Analogously, we compute \sigma_{p^k} for the canonical primitive root modulo (p^k) for positive integers k, and compute \rho(p^k, b) for b dividing (p - 1), accordingly.
##############################################################
msg.allGroupsP2Q := function(n)
local fac, p, q, all, a, b, c, d, r1, R1, r2, R2, r3, R3, G, k, ii, qq, mat, list;
####
	fac := Factors(n);
	if not Length(fac) = 3 or fac[1] = fac[3] then
			Error("Argument has to be of the form p^2*q, where p, q are primes");
	fi;
	p := fac[2];
	if fac[2] = fac[1] then
		q := fac[3];
	else
		q := fac[1];
	fi;
	if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) then
		Error("wrong input");
	fi;
#### computing canonical roots:
	a := Z(p);
	b := Z(q);
	if not Int(a^(p - 1)) mod p^2 = 1 then
		d := ZmodnZObj(Int(a), p^2);
	else d := ZmodnZObj(Int(a) + p, p^2);
	fi;
	if (p - 1) mod q = 0 then
		r1 := a^((p-1)/q);
		R1 := Int(r1);
	fi;
	if (q - 1) mod p = 0 then
		r2 := b^((q - 1)/p);
		R2 := Int(r2);
		if (q - 1) mod p^2 = 0 then
			r3 := b^((q - 1)/(p^2));
			R3 := Int(r3);
		fi;
	fi;
##case 0: abelian groups are isomorphic to direct product P \times Q:
	all := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];
##case 1: nonabelian, p > q > 2 and q divides (p + 1): such case exists only if P \cong C_p^2, and Q acts irreducibly on P:
	if p > q and q > 2 and (p + 1) mod q = 0 then
		mat := msg.QthRootGL2P(p, q);
	 Add(all, [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ]);
	fi;
####case 2: nonabelian, p > q > 2, and q divides (p - 1): it follows that G has a normal Sylow p-subgroup, that is, P is normal.
#There are two cases to consider depending on the isomorphism type of P.
	if (p - 1) mod q = 0 and q > 2 then
		Add(all, [ [q, p, p], [2, 1, [2, R1]] ]); ##(C_q \ltimes C_p) times C_p
		for k in [0..(q - 1)/2] do
			Add(all, [ [q, p, p], [2, 1, [2, R1]], [3, 1, [3, Int(r1^(Int(b^k)))]] ]); ##C_q \ltimes C_p^2
		od;
		ii := Int(d^(p*(p-1)/q)) mod p;
		qq := (Int(d^(p*(p-1)/q)) - ii)/p;
		Add(all, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
	fi;
####case 3: nonabelian, p > q and q = 2: in this case, P is normal in G.
	if p > q and q = 2 then
		Append(all, [ [ [2, p, p], [2, 1, [2, p - 1]] ], ##D_p \times C_p
		[ [2, p, p], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ], ##C_2 \ltimes C_p^2
		[ [2, p, p], [2, [3, 1]], [2, 1, [2, p - 1, 3, p - 1]], [3, 1, [3, p - 1]] ] ]); ##D_{p^2}
	fi;
####order 12: nonabelian, could be checked by exhaustion.
	if p = 2 and q = 3 then
		Append(all, [ [ [3, 2, 2], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ], [ [2, 2, 3], [2, [3, 1]], [2, 1, [2, 1, 3, 2]], [3, 1, [3, 2]] ], [ [2, 2, 3], [1, [2, 1]], [3, 1, [3, 2]] ] ]);
	fi;
####case4: nonabelian, q > p and q > 3: in this case, Q is normal in G.
	if (q - 1) mod p = 0 and q > 3 then
		Append(all, [ [ [p, p, q], [3, 1, [3, R2]] ], ##C_p \times (C_p \ltimes C_q)
		[ [p, p, q], [1, [2, 1]], [3, 1, [3, R2]] ] ]); ## C_{p^2} \ltimes C_q
	fi;
	if (q - 1) mod (p^2) = 0 then
		Add(all, [ [p, p, q], [1, [2, 1]], [3, 1, [3, R3]], [3, 2, [3, R2]]]); ## C_{p^2} \ltimes C_q
	fi;

	list := List(all, x -> msg.groupFromData(x));
	return list;
end;

######################################################
msg.NumberGroupsP2Q := function(n)
  local fac, p, q, w;
    fac := Factors(n);
    if not Length(fac) = 3 or fac[1] = fac[3] then
      Error("Argument has to be of the form p^2*q, where p, q are primes"); fi;
      p := fac[2];
      if fac[2] = fac[1] then
      q := fac[3];
      else
      q := fac[1];
      fi;
    if q = 2 then w := 5;
    elif p > q then w := 2 + msg.w((p+1), q) + (q+5)*msg.w((p-1), q)/2;
    else w := 2 + 2*msg.w((q-1), p) + msg.w((p+1), q) + msg.w((q-1), p^2);
    fi;
  return w;
end;
######################################################

msg.isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i->  i[2]) in [ [ 2, 1 ], [ 1, 2 ] ];

##############################################################
msg.GroupP2Q := function(n, i)
local fac, p, q, all, a, b, c, d, G, k, r1, R1, r2, R2, r3, R3, ii, qq, mat, l0, c1, l1, c2, l2, c3, l3, c4, l4, data;
####
	fac := Factors(n);
	if not Length(fac) = 3 or fac[1] = fac[3] then
			Error("Argument has to be of the form p^2*q, where p, q are primes");
	fi;
	p := fac[2];
	if fac[2] = fac[1] then
		q := fac[3];
	else
		q := fac[1];
	fi;
	a := Z(p);
	b := Z(q);
	if not Int(a)^(p - 1) mod p^2 = 1 then
		d := ZmodnZObj(Int(a), p^2);
	else d := ZmodnZObj(Int(a) + p, p^2);
	fi;

	if (p - 1) mod q = 0 then
		r1 := a^((p-1)/q);
		R1 := Int(r1);
	fi;
	if (q - 1) mod p = 0 then
		r2 := b^((q - 1)/p);
		R2 := Int(r2);
		if (q - 1) mod p^2 = 0 then
			r3 := b^((q - 1)/(p^2));
			R3 := Int(r3);
		fi;
	fi;

	if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) then
		Error("wrong input");
	fi;
####enumeration:
	c1 := msg.w((p + 1), q);
	c2 := 1/2*(q + 5)*msg.w((p - 1), q);
	c3 := 3*msg.delta(q, 2);
	c4 := 2*msg.w((q - 1), p)*(1 - msg.delta(q, 3)) + msg.w((q - 1), p^2);
	if i < 3 then
		l0 := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];
		data := l0[i];
		return msg.groupFromData(data);
###case 1: p > q > 2 and q divides (p + 1)
	elif p > q and q > 2 and (p + 1) mod q = 0 and i = 3 then
		mat := msg.QthRootGL2P(p, q);
		data := [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ];
		return msg.groupFromData(data);

####case 2 : p > q > 2, and q divides (p - 1)
	elif (p - 1) mod q = 0 and q > 2 and i > 2 and i < (3 + c2) then
		l2 := [];
		Add(l2, [ [q, p, p], [2, 1, [2, R1]] ]); ##(C_q \ltimes C_p) times C_p
		for k in [0..(q - 1)/2] do
			Add(l2, [ [q, p, p], [2, 1, [2, R1]], [3, 1, [3, Int(r1^(Int(b^k)))]] ]); ##C_q \ltimes C_p^2
		od;
		ii := Int(d^(p*(p-1)/q)) mod p;
		qq := (Int(d^(p*(p-1)/q)) - ii)/p;
		Add(l2, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
		data := l2[i - 2];
		return msg.groupFromData(data);

####case 3: p > q and q = 2
	elif p > q and q = 2 and i > 2 and i < 6 then
		l3 := [];
		Append(l3, [ [ [2, p, p], [2, 1, [2, p - 1]] ], ##D_p \times C_p
		[ [2, p, p], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ], ##C_2 \ltimes C_p^2
		[ [2, p, p], [2, [3, 1]], [2, 1, [2, p - 1, 3, p - 1]], [3, 1, [3, p - 1]] ] ]); ##D_{p^2}
		data := l3[i - 2];
		return msg.groupFromData(data);

####order 12
	elif p = 2 and q = 3 and i > 2 and i < 6 then
		data := [ [ [3, 2, 2], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ],
		[ [2, 2, 3], [2, [3, 1]], [2, 1, [2, 1, 3, 2]], [3, 1, [3, 2]] ],
		[ [2, 2, 3], [1, [2, 1]], [3, 1, [3, 2]] ] ][i - 2];
		return msg.groupFromData(data);

####case4: q > p and q > 3
	elif (q - 1) mod p = 0 and q > 3 and i > 2 and i < (3 + c4) then
		l4 := [];
		Append(l4, [ [ [p, p, q], [3, 1, [3, R2]] ], ##C_p \times (C_p \ltimes C_q)
		[ [p, p, q], [1, [2, 1]], [3, 1, [3, R2]] ] ]); ## C_{p^2} \ltimes C_q
		if (q - 1) mod (p^2) = 0 then
			Add(l4, [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(b^((q - 1)/(p^2)))]], [3, 2, [3, R2]]]); ## C_{p^2} \ltimes C_q
		fi;
		data := l4[i - 2];
		return msg.groupFromData(data);
	fi;

end;
