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
SOTRec.allGroupsP2Q := function(p, q)
local all, a, b, c, d, r1, R1, r2, R2, r3, R3, G, k, ii, qq, mat, list;
####
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
#### computing canonical roots:
	a := Z(p);
	b := Z(q);
	if not Int(a^(p - 1)) mod p^2 = 1 then
		d := ZmodnZObj(Int(a), p^2);
	else
	    d := ZmodnZObj(Int(a) + p, p^2);
	fi;
	if (p - 1) mod q = 0 then
		## \rho(p, q)
		r1 := a^((p-1)/q);
		R1 := Int(r1);
	fi;
	if (q - 1) mod p = 0 then
		## \rho(q, p)
		r2 := b^((q - 1)/p);
		R2 := Int(r2);
		if (q - 1) mod p^2 = 0 then
			## \rho(q, p^2)
			r3 := b^((q - 1)/(p^2));
			R3 := Int(r3);
		fi;
	fi;
##Cluster 1: nilpotent groups, which are isomorphic to direct product P \times Q:
## type [ppq, p^q]
	all := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];

##Cluster 2: non-nilpotent groups with a normal Sylow p-subgroup that is isomorphic to C_p^2
	if (p - 1) mod q = 0 then
		Add(all, [ [q, p, p], [2, 1, [2, R1]] ]); ##(C_q \ltimes C_p) times C_p
		for k in [0..Int((q - 1)/2)] do
			Add(all, [ [q, p, p], [2, 1, [2, R1]], [3, 1, [3, Int(r1^(Int(b^k)))]] ]); ##C_q \ltimes C_p^2
		od;
	elif (p + 1) mod q = 0 and q > 2 then
		mat := SOTRec.QthRootGL2P(p, q);
		Add(all, [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ]);
	fi;

##Cluster 3: non-nilpotent groups with a normal Sylow p-subgroup that is isomorphic to C_{p^2}
	if (p - 1) mod q = 0 then
		ii := Int(d^(p*(p-1)/q)) mod p;
		qq := (Int(d^(p*(p-1)/q)) - ii)/p;
		Add(all, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
	fi;

##Cluster 4: non-nilpotent groups with a normal Sylow q-subgroup whose complement is isomorphic to C_p^2
	if (q - 1) mod p = 0 then
		Add(all, [ [p, p, q], [3, 1, [3, R2]] ]); ##C_p \times (C_p \ltimes C_q)
	fi;

##Cluster 5: non-nilpotent groups with a normal Sylow q-subgroup whose complement is isomorphic to C_p^2
	if (q - 1) mod p = 0 then
		Add(all, [ [p, p, q], [1, [2, 1]], [3, 1, [3, R2]] ]); ##C_p \times (C_p \ltimes C_q)
	fi;
	if (q - 1) mod (p^2) = 0 then
		Add(all, [ [p, p, q], [1, [2, 1]], [3, 1, [3, R3]], [3, 2, [3, R2]]]); ## C_{p^2} \ltimes C_q
	fi;

	list := List(all, x -> SOTRec.groupFromData(x));
	return list;
end;

######################################################
SOTRec.NumberGroupsP2Q := function(p, q)
  local w;
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    if q = 2 then
      w := 5;
    elif p > q then
      w := 2 + SOTRec.w((p+1), q) + (q+5)*SOTRec.w((p-1), q)/2;
    else
      w := 2 + SOTRec.w((p+1), q) + 2*SOTRec.w((q-1), p) + SOTRec.w((q-1), p^2);
    fi;
  return w;
end;
######################################################

SOTRec.isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i->  i[2]) in [ [ 2, 1 ], [ 1, 2 ] ];

##############################################################
SOTRec.GroupP2Q := function(p, q, i)
local all, a, b, c, d, G, k, r1, R1, r2, R2, r3, R3, ii, qq, mat, l0, c1, l1, c2, l2, c3, l3, c4, l4, c5, l5, data;
####
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

	a := Z(p);
	b := Z(q);
	if not Int(a)^(p - 1) mod p^2 = 1 then
		d := ZmodnZObj(Int(a), p^2);
	else
	    d := ZmodnZObj(Int(a) + p, p^2);
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
	c1 := 2;
	c2 := 1/2*(q + 3 - SOTRec.w(q, 2))*SOTRec.w((p - 1), q) + (1 - SOTRec.w(q, 2))*SOTRec.w((p + 1), q);
	c3 := SOTRec.w((p - 1), q);
	c4 := SOTRec.w((q - 1), p);
	c5 := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
####Cluster 1: nilpotent
	if i < c1 + 1 then
		l1 := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];
		data := l1[i];
		return SOTRec.groupFromData(data);
###Cluster 2: non-nilpotent, normal P \cong C_p^2
	elif i > c1 and i < c1 + c2 + 1 then
		l2 := [];
		if (p - 1) mod q = 0 then
			Add(l2, [ [q, p, p], [2, 1, [2, R1]] ]); ##(C_q \ltimes C_p) times C_p
			for k in [0..Int((q - 1)/2)] do
				Add(l2, [ [q, p, p], [2, 1, [2, R1]], [3, 1, [3, Int(r1^(Int(b^k)))]] ]); ##C_q \ltimes C_p^2
			od;
		elif (p + 1) mod q = 0 and q > 2 then
			mat := SOTRec.QthRootGL2P(p, q);
			Add(l2, [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ]);
		fi;
		data := l2[i - c1];
		return SOTRec.groupFromData(data);

####Cluster 3: non-nilpotent, normal P \cong C_{p^2}
	elif i > c1 + c2 and i < (c1 + c2 + c3 + 1) then
		l3 := [];
		if (p - 1) mod q = 0 then
			ii := Int(d^(p*(p-1)/q)) mod p;
			qq := (Int(d^(p*(p-1)/q)) - ii)/p;
			Add(l3, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
		fi;
		data := l3[i - c1 - c2];
		return SOTRec.groupFromData(data);

####Cluster 4: non-nilpotent, normal Q with complement \cong C_p^2
	elif i > c1 + c2 + c3 and i < (c1 + c2 + c3 + c4 + 1) then
		l4 := [];
		if (q - 1) mod p = 0 then
			Add(l4, [ [p, p, q], [3, 1, [3, R2]] ]); ##C_p \times (C_p \ltimes C_q)
		fi;
		data := l4[i - c1 - c2 - c3];
		return SOTRec.groupFromData(data);

####Cluster 4: non-nilpotent, normal Q with complement \cong C_{p^2}
	elif i > c1 + c2 + c3 + c4 and i < (c1 + c2 + c3 + c4 + c5 + 1) then
		l5 := [];
		if (q - 1) mod p = 0 then
			Add(l5, [ [p, p, q], [1, [2, 1]], [3, 1, [3, R2]] ]); ##C_p \times (C_p \ltimes C_q)
		fi;
		if (q - 1) mod (p^2) = 0 then
			Add(l5, [ [p, p, q], [1, [2, 1]], [3, 1, [3, R3]], [3, 2, [3, R2]]]); ## C_{p^2} \ltimes C_q
		fi;
		data := l5[i - c1 - c2 - c3 - c4];
		return SOTRec.groupFromData(data);
	fi;

end;
