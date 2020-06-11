##############################################################
msg.allGroupsP2Q := function(n)
local fac, p, q, all, a, b, c, d, G, k, ii, qq, mat, list;
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
####
	a := Z(p);
	b := Z(q);
	c := ZmodnZObj(Int(Z(p)),p^2);
	if not c^(p - 1) = ZmodnZObj(1, p^2) then
		d := c; else d := c + 1;
	fi;
	all := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];
##case 1: p > q > 2 and q divides (p + 1)
	if p > q and q > 2 and (p + 1) mod q = 0 then
		mat := msg.QthRootGL2P(p, q);
	 Add(all, [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ]);
	fi;
####case 2 : p > q > 2, and q divides (p - 1)
	if (p - 1) mod q = 0 and q > 2 then
		Add(all, [ [q, p, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ]); ##(C_q \ltimes C_p) times C_p
		for k in [0..(q - 1)/2] do
			Add(all, [ [q, p, p], [2, 1, [2, Int(a^((p-1)/q))]], [3, 1, [3, Int(a^(Int(b^k)*(p-1)/q))]] ]); ##C_q \ltimes C_p^2
		od;
		ii := Int(d^(p*(p-1)/q)) mod p;
		qq := (Int(d^(p*(p-1)/q)) - ii)/p;
		Add(all, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
	fi;
####case 3: p > q and q = 2
	if p > q and q = 2 then
		Append(all, [ [ [2, p, p], [2, 1, [2, p - 1]] ], ##D_p \times C_p
		[ [2, p, p], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ], ##C_2 \ltimes C_p^2
		[ [2, p, p], [2, [3, 1]], [2, 1, [2, p - 1, 3, p - 1]], [3, 1, [3, p - 1]] ] ]); ##D_{p^2}
	fi;
####order 12
	if p = 2 and q = 3 then
		Append(all, [ [ [3, 2, 2], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ], [ [2, 2, 3], [2, [3, 1]], [2, 1, [2, 1, 3, 2]], [3, 1, [3, 2]] ], [ [2, 2, 3], [1, [2, 1]], [3, 1, [3, 2]] ] ]);
	fi;
####case4: q > p and q > 3
	if (q - 1) mod p = 0 and q > 3 then
		Append(all, [ [ [p, p, q], [3, 1, [3, Int(b^((q - 1)/p))]] ], ##C_p \times (C_p \ltimes C_q)
		[ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(b^((q - 1)/p))]] ] ]); ## C_{p^2} \ltimes C_q
	fi;
	if (q - 1) mod (p^2) = 0 then
		Add(all, [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(b^((q - 1)/(p^2)))]], [3, 2, [3, Int(b^((q - 1)/p))]]]); ## C_{p^2} \ltimes C_q
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
    elif p > q then w := 2 + msg.deltaDivisibility((p+1), q) + (q+5)*msg.deltaDivisibility((p-1), q)/2;
    else w := 2 + 2*msg.deltaDivisibility((q-1), p) + msg.deltaDivisibility((p+1), q) + msg.deltaDivisibility((q-1), p^2);
    fi;
  return w;
end;
######################################################

msg.isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i->  i[2]) in [ [ 2, 1 ], [ 1, 2 ] ];

##############################################################

msg.GroupP2Q := function(n, i)
	local fac, p, q, all, a, b, c, d, G, k, ii, qq, mat;
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
####
    a := Z(p);
    b := Z(q);
    c := ZmodnZObj(Int(Z(p)),p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c; else d := c + 1;
    fi;
    all := [ [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, q], [2, [3, 1]] ] ];
##case 1: p > q > 2 and q divides (p + 1)
    if p > q and q > 2 and (p + 1) mod q = 0 then
			mat := msg.QthRootGL2P(p, q);
     Add(all, [ [q, p, p], [2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]], [3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]] ]);
    fi;
####case 2 : p > q > 2, and q divides (p - 1)
    if (p - 1) mod q = 0 and q > 2 then
      Add(all, [ [q, p, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ]); ##(C_q \ltimes C_p) times C_p
      for k in [0..(q - 1)/2] do
        Add(all, [ [q, p, p], [2, 1, [2, Int(a^((p-1)/q))]], [3, 1, [3, Int(a^(Int(b^k)*(p-1)/q))]] ]); ##C_q \ltimes C_p^2
      od;
      ii := Int(d^(p*(p-1)/q)) mod p;
      qq := (Int(d^(p*(p-1)/q)) - ii)/p;
      Add(all, [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
    fi;
####case 3: p > q and q = 2
    if p > q and q = 2 then
      Append(all, [ [ [2, p, p], [2, 1, [2, p - 1]] ], ##D_p \times C_p
      [ [2, p, p], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ], ##C_2 \ltimes C_p^2
      [ [2, p, p], [2, [3, 1]], [2, 1, [2, p - 1, 3, p - 1]], [3, 1, [3, p - 1]] ] ]); ##D_{p^2}
    fi;
####order 12
    if p = 2 and q = 3 then
      Append(all, [ [ [3, 2, 2], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ], [ [2, 2, 3], [2, [3, 1]], [2, 1, [2, 1, 3, 2]], [3, 1, [3, 2]] ], [ [2, 2, 3], [1, [2, 1]], [3, 1, [3, 2]] ] ]);
    fi;
####case4: q > p and q > 3
    if (q - 1) mod p = 0 and q > 3 then
      Append(all, [ [ [p, p, q], [3, 1, [3, Int(b^((q - 1)/p))]] ], ##C_p \times (C_p \ltimes C_q)
      [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(b^((q - 1)/p))]] ] ]); ## C_{p^2} \ltimes C_q
    fi;
    if (q - 1) mod (p^2) = 0 then
      Add(all, [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(b^((q - 1)/(p^2)))]], [3, 2, [3, Int(b^((q - 1)/p))]]]); ## C_{p^2} \ltimes C_q
    fi;

    if i < (msg.NumberGroupsP2Q(n) + 1) then
      G := msg.groupFromData(all[i]);
		fi;
	return G;
end;
