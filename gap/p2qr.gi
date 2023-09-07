## The following functions contribute to AllSOTGroups, NumberOfSOTGroups, and SOTGroup, respectively.
## Let G be a group of order p^2qr (p, q, r are distinct primes and q < r).
  ## Since G is cubefree, G is nilpotent if and only if G is abelian.
  ## By examining the composition series (with simple factors) of G, we observe that G is nonsolvable if and only if it is isomorphic to \Alt_5.
  ## If G is non-nilpotent and solvable, then it has a nontrivial, abelian Fitting subgroup, denoted by F.
  ## By [2, Lemma 3.7], we know G/F acts faithfully on F, that is, G/F embeds into Aut(F).
  ## We deduce that |F| \in \{r, qr, p^2, p^2q, p^2r, pr, pqr\}.
  ## For each case depending on the size of F, we construct the isomorphism types of non-nilpotent, solvable groups G.
  ## For further details, see [2, Section 3.2 & 3.7].

SOTRec.allGroupsP2QR := function(p, q, r)
local a, b, c, u, v, ii, qq, iii, qqq, k, l, Rootpr, Rootpq, Rootrq, Rootrp, Rootrp2, Rootqp, Rootqp2,
  rootpr, rootpq, rootrq, rootrp, rootrp2, rootqp, rootqp2, matq, matr, matqr, mat, mat_k, all, list;
    ####
    Assert(1, r > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));

    a := Z(r); #\sigma_r
    b := Z(p); #\sigma_p
    c := Z(q); #\sigma_q

    u := ZmodnZObj(Int(Z(p)), p^2);
    if not u^(p-1) = ZmodnZObj(1, p^2) then
      v := u;
    else
      v := u + 1;
    fi;
    if (p - 1) mod q = 0 then
      ii := Int(v^((p^2-p)/q)) mod p;
      qq := (Int(v^((p^2-p)/q)) - ii)/p;
    fi;
    if (p - 1) mod r = 0 then
      iii := Int(v^((p^2-p)/r)) mod p;
      qqq := (Int(v^((p^2-p)/r)) - iii)/p;
    fi;

    if (p + 1) mod (q * r) = 0 and q > 2 then
      matqr := SOTRec.QthRootGL2P(p, (q*r));
      mat := matqr^q;
    fi;
    if (p + 1) mod r = 0 and r > 2 then
      matr := SOTRec.QthRootGL2P(p, r);
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      matq := SOTRec.QthRootGL2P(p, q);
    fi;
############ abelian groups:
    all := [ [ [p, p, q, r], [1, [2, 1]] ], [ [p, p, q, r] ] ];
############ precompute canonical roots:
    if (r - 1) mod p = 0 then
      rootrp := a^((r-1)/p);
      Rootrp := Int(rootrp);
    fi; #\rho(r, p)
    if (r - 1) mod (p^2) = 0 then
      rootrp2 := a^((r-1)/(p^2));
      Rootrp2 := Int(rootrp2);
    fi; #\rho(r, p^2)
    if (r - 1) mod q = 0 then
      rootrq := a^((r-1)/q);
      Rootrq := Int(rootrq);
    fi; #\rho(r, q)
    if (p - 1) mod r = 0 then
      rootpr := b^((p-1)/r);
      Rootpr := Int(rootpr);
    fi; #\rho(p, r)
    if (p - 1) mod q = 0 then
      rootpq := b^((p-1)/q);
      Rootpq := Int(rootpq);
    fi; #\rho(p, q)
    if (q - 1) mod p = 0 then
      rootqp := c^((q-1)/p);
      Rootqp := Int(rootqp);
    fi; #\rho(q, p)
    if (q - 1) mod (p^2) = 0 then
      rootqp2 := c^((q-1)/(p^2));
      Rootqp2 := Int(rootqp2);
    fi; #\rho(q, p^2)

############ case 1: nonabelian and Fitting subgroup has order r -- p^2q | (r - 1), unique up to isomorphism
    if (r - 1) mod (p^2*q) = 0 then ##C_{p^2q} \ltimes C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(a^((r-1)/(p^2*q)))]], [4, 2, [4, Int(a^((r-1)/(p*q)))]], [4, 3, [4, Rootrq]] ]);
    fi;

############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or p | (q - 1)(r - 1)
    if (q - 1) mod (p^2) = 0 then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]] ]);
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
      od;
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in SOTRec.groupofunitsP2(p) do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]], [4, 1, [4, Int(rootrp2^k)]], [4, 2, [4, Int(rootrp^k)]] ]);
      od;
    fi;
    if (r - 1) mod (p^2) = 0 then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Rootrp2]], [4, 2, [4, Rootrp]] ]);
    fi;
    if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1]
        do Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp2^k)]], [4, 2, [4, Int(rootrp^k)]] ]);
      od;
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
      Add(all, [ [p, p, q, r], [3, 1, [3, Rootqp]], [4, 2, [4, Rootrp]] ]);
    fi;

############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
      Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [4, 2, [4, Rootpr]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
      Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(q - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^k)]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(r - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 2, [4, Int(rootpr^k)]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q > 2 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [0..(q - 1)/2] do
        for l in [0..(r - 1)/2] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^(Int(c^k)))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p - 1) mod (q*r) =0 and q > 2 then
      for k in [1..(q-3)/2] do
        for l in [(r+1)/2..(r-2)] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^(Int(c^k)))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then
      for l in [0..(r-1)/2] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Rootpq]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then ##q = 2, r | (p - 1), and G \cong D_r \ltimes C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Rootpr]], [4, 1, [3, 1]], [4, 2, [4, Int(rootpr^(-1))]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q > 2 then ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
      Add(all, [ [q, r, p, p], [1, [2, 1]],
      [3, 1, [3, Int(matqr[1][1]), 4, Int(matqr[2][1])]],
      [4, 1, [3, Int(matqr[1][2]), 4, Int(matqr[2][2])]],
      [3, 2, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
      [4, 2, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
      Add(all, [ [q, r, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong (C_q \ltimes C_r)\ltimes C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [4, 1, [3, 1]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p], [3, 1, [3, Rootpq]], [4, 1, [4, Rootpq]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
      [3, 2, [3, Rootpr]], [4, 2, [4, Rootpr]] ]);
    fi;

############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
      Add(all, [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ]);
    fi;
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
      Add(all, [ [r, p, p, q], [2, 1, [2, Rootpr]] ]);
    fi;
    if (p - 1) mod r = 0 and r > 2 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      for k in [0..(r - 1)/2] do
       Add(all, [ [r, p, p, q], [2, 1, [2, Rootpr]], [3, 1, [3, Int(rootpr^(Int(a^k)))]] ]);
      od;
    fi;
    if (p + 1) mod r = 0 and r > 2 then ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      Add(all, [ [r, p, p, q],
      [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
      [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ]);
    fi;

############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    if (r - 1) mod q = 0 then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Rootrq]] ]);
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
      Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
    fi;
    if (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
      for k in [1..(q-1)] do
        Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(rootrq^k)]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
      Add(all, [ [q, p, p, r], [2, 1, [2, Rootpq]] ]);
    fi;
    if (p - 1) mod q = 0 and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
      for k in [0..(q - 1)/2] do
       Add(all, [ [q, p, p, r], [2, 1, [2, Rootpq]], [3, 1, [3, Int(rootpq^(Int(c^k)))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q = 2 then
      Add(all, [ [q, p, p, r], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ]);
    fi;
    if (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]], [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;
    if (r - 1) mod q = 0 then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, Rootrq]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
      for k in [1..q - 1] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Int(rootpq^k)]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [0..(q - 3)/2] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [1..(q - 3)/2] do
        for k in [0..(q - 1)/2] do
            Add(all, [ [q, r, p, p], [2, 1, [2, Int(rootrq^(Int(c^l)))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
        od;
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^((q - 1)/2))*(r-1)/q))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(b^(Int(c^((q - 1)/2))*(p-1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [(q - 1)/2..q - 2] do
        for k in [0..(q - 3)/2] do
          Add(all, [ [q, r, p, p], [2, 1, [2, Int(rootrq^(Int(c^l)))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
        od;
      od;
    fi;
    if q = 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, r - 1]], [3, 1, [3, Rootpq]], [4, 1, [4, Rootpq]] ]);
    fi;
    if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [1..(q-1)/2] do
        mat_k := matq^k;
        Add(all, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Int(mat_k[1][1]), 4, Int(mat_k[2][1])]], [4, 1, [3, Int(mat_k[1][2]), 4, Int(mat_k[2][2])]] ]);
      od;
    fi;

############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [4, 1, [4, Rootrp]], [4, 2, [4, Rootrq]] ]);
    fi;
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Rootrp]], [4, 2, [4, Rootrq]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
      Add(all, [ [p, r, q, p], [2, 1, [2, Rootrp]], [4, 3, [4, Rootpq]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
      for k in [1..q-1] do
        Add(all, [ [p, q, r, p], [3, 1, [3, Rootrp]], [3, 2, [3, Rootrq]], [4, 2, [4, Int(rootpq^k)]] ]);
      od;
    fi;

############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if (r - 1) mod p = 0 then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Rootrp]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
      od;
    fi;

    if (r - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [4, 1, [4, Rootrp]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_r
      Add(all, [ [p, p, q, r], [3, 1, [3, Rootqp]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_p^2 and G \cong C_p^2 \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
      od;
    fi;

############
    list := List(all, x->SOTRec.groupFromData(x));
    if p = 2 and q = 3 and r = 5 then
      Add(list, AlternatingGroup(5));
    fi;
  return list;
end;

######################################################
SOTRec.NumberGroupsP2QR := function(p, q, r)
  local m;
    if p = 2 and q = 3 and r = 5 then
      m := 13;
    elif q = 2 then
      m := 10 + (2*r + 7)*SOTRec.w((p - 1), r)
              + 3*SOTRec.w((p + 1), r)
              + 6*SOTRec.w((r - 1), p)
              + 2*SOTRec.w((r - 1), (p^2));
    elif q > 2 and not (p = 2 and q = 3 and r = 5) then
      m := 2 + (p^2 - p)*SOTRec.w((q - 1), (p^2))*SOTRec.w((r - 1), (p^2))
             + (p - 1)*(SOTRec.w((q - 1), (p^2))*SOTRec.w((r - 1), p) + SOTRec.w((r - 1), (p^2))*SOTRec.w((q - 1), p)
             + 2*SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p))
             + (q - 1)*(q + 4)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)/2
             + (q - 1)*(SOTRec.w((p + 1), q)*SOTRec.w((r - 1), q)
             + SOTRec.w((p - 1), q)
             + SOTRec.w((p - 1), (q*r))
             + 2*SOTRec.w((r - 1), (p*q))*SOTRec.w((p - 1), q))/2
             + (q*r + 1)*SOTRec.w((p - 1), (q*r))/2
             + (r + 5)*SOTRec.w((p - 1), r)*(1 + SOTRec.w((p - 1), q))/2
             + SOTRec.w((p^2 - 1), (q*r))
             + 2*SOTRec.w((r - 1), (p*q))
             + SOTRec.w((r - 1), p)*SOTRec.w((p - 1), q)
             + SOTRec.w((r - 1), (p^2*q))
             + SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p)
             + 2*SOTRec.w((q - 1), p)
             + 3*SOTRec.w((p - 1), q)
             + 2*SOTRec.w((r - 1), p)
             + 2*SOTRec.w((r - 1), q)
             + SOTRec.w((r - 1), (p^2))
             + SOTRec.w((q - 1), p^2)
             + SOTRec.w((p + 1), r)
             + SOTRec.w((p + 1), q);
    fi;
    return m;
  end;
######################################################
######################################################
SOTRec.GroupP2QR := function(p, q, r, i)
local a, b, c, u, v, ii, qq, iii, qqq, k, l, matq, matr, matqr, mat, mat_k,
    Rootpr, Rootpq, Rootrq, Rootrp, Rootrp2, Rootqp, Rootqp2, rootpr, rootpq, rootrq, rootrp, rootrp2, rootqp, rootqp2,
    c1, c2, c3, c4, c5, c6, c7, l1, l2, l3, l4, l5, l6, l7, l0, data, G;

    ####
    Assert(1, r > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    Assert(1, IsPrimeInt(r));

############ precompute Roots:
    a := Z(r);
    b := Z(p);
    c := Z(q);

    if (r - 1) mod p = 0 then
      rootrp := a^((r-1)/p);
      Rootrp := Int(rootrp);
    fi;
    if (r - 1) mod (p^2) = 0 then
      rootrp2 := a^((r-1)/(p^2));
      Rootrp2 := Int(rootrp2);
    fi;
    if (r - 1) mod q = 0 then
      rootrq := a^((r-1)/q);
      Rootrq := Int(rootrq);
    fi;
    if (p - 1) mod r = 0 then
      rootpr := b^((p-1)/r);
      Rootpr := Int(rootpr);
    fi;
    if (p - 1) mod q = 0 then
      rootpq := b^((p-1)/q);
      Rootpq := Int(rootpq);
    fi;
    if (q - 1) mod p = 0 then
      rootqp := c^((q-1)/p);
      Rootqp := Int(rootqp);
    fi;
    if (q - 1) mod (p^2) = 0 then
      rootqp2 := c^((q-1)/(p^2));
      Rootqp2 := Int(rootqp2);
    fi;

    if not Int(b)^(p-1) mod p^2 = 1 then
      v := ZmodnZObj(Int(b), p^2);
    else
      v := ZmodnZObj(Int(b) + p, p^2);
    fi;
    if (p - 1) mod q = 0 then
      ii := Int(v^((p^2-p)/q)) mod p;
      qq := (Int(v^((p^2-p)/q)) - ii)/p;
    fi;
    if (p - 1) mod r = 0 then
      iii := Int(v^((p^2-p)/r)) mod p;
      qqq := (Int(v^((p^2-p)/r)) - iii)/p;
    fi;

    if (p + 1) mod (q * r) = 0 and q > 2 then
      matqr := SOTRec.QthRootGL2P(p, (q*r));
      mat := matqr^q;
    fi;
    if (p + 1) mod r = 0 and r > 2 then
      matr := SOTRec.QthRootGL2P(p, r);
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      matq := SOTRec.QthRootGL2P(p, q);
    fi;
############ enumeration of distinct cases
    c1 := SOTRec.w((r - 1), p^2*q);;
    c2 := SOTRec.w((q - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p^2)*SOTRec.w((r - 1), p)
    + (p^2 - p)*SOTRec.w((r - 1), p^2)*SOTRec.w((q - 1), p^2)
    + SOTRec.w((r - 1), p^2) + (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p^2)
    + SOTRec.w((r - 1), p)*SOTRec.w((q - 1), p);;
    c3 := 1/2*(q*r+q+r+7)*SOTRec.w((p - 1), q*r)
    + SOTRec.w((p^2 - 1), q*r)*(1 - SOTRec.w((p - 1), q*r))*(1 - SOTRec.delta(q, 2))
    + 2*SOTRec.w((p + 1), r)*SOTRec.delta(q, 2);;
    c4 := 1/2*(r + 5)*SOTRec.w((p - 1), r) + SOTRec.w((p + 1), r);;
    c5 := 8*SOTRec.delta(q, 2)
    + (1 - SOTRec.delta(q, 2))*(1/2*(q - 1)*(q + 4)*SOTRec.w((p - 1), q)*SOTRec.w((r - 1), q)
    + 1/2*(q - 1)*SOTRec.w((p + 1), q)*SOTRec.w((r - 1), q)
    + 1/2*(q + 5)*SOTRec.w((p - 1), q)
    + 2*SOTRec.w((r - 1), q)
    + SOTRec.w((p + 1), q));;
    c6 := SOTRec.w((r - 1), p)*(SOTRec.w((p - 1), q)*(1 + (q - 1)*SOTRec.w((r - 1), q))
    + 2*SOTRec.w((r - 1), q));;
    c7 := 2*(SOTRec.w((q - 1), p) + SOTRec.w((r - 1), p) +
    (p - 1)*SOTRec.w((q - 1), p)*SOTRec.w((r - 1), p));

############ add abelian groups in:
    l0 := [ [ [p, p, q, r], [1, [2, 1]] ], [ [p, p, q, r] ] ];
    if i < 3 then
      G := SOTRec.groupFromData(l0[i]);
      return G;
    fi;
############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
    if (r - 1) mod (p^2*q) = 0 and i > 2 and i < (3 + c1) then ##C_{p^2q} \ltimes C_r
      l1 := [];
      Add(l1, [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(a^((r-1)/(p^2*q)))]], [4, 2, [4, Int(a^((r-1)/(p*q)))]], [4, 3, [4, Rootrq]] ]);
      data := l1[i - 2];
      return SOTRec.groupFromData(data);
    fi;

############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or (p^2 | (q - 1) or (r - 1)) or (p | (q - 1) and p | (r - 1))
    if i > (2 + c1) and i < (3 + c1 + c2) then
      l2 := [];
      if (q - 1) mod (p^2) = 0 then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
        Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]] ]);
      fi;
      if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
        od;
      fi;
      if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in SOTRec.groupofunitsP2(p) do
          Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp2]], [3, 2, [3, Rootqp]], [4, 1, [4, Int(rootrp2^k)]], [4, 2, [4, Int(rootrp^k)]] ]);
        od;
      fi;
      if (r - 1) mod (p^2) = 0 then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
        Add(l2, [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Rootrp2]], [4, 2, [4, Rootrp]] ]);
      fi;
      if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1]
          do Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp2^k)]], [4, 2, [4, Int(rootrp^k)]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
        Add(l2, [ [p, p, q, r], [3, 1, [3, Rootqp]], [4, 2, [4, Rootrp]] ]);
      fi;
      data := l2[i - 2 - c1];
      return SOTRec.groupFromData(data);
    fi;

############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    if i > (2 + c1 + c2) and i < (3 + c1 + c2 + c3) then
      l3 := [];
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
        Add(l3, [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
        Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [4, 2, [4, Rootpr]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
        Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [1..(q - 1)] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^k)]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [1..(r - 1)] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 2, [4, Int(rootpr^k)]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q > 2 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [0..(q - 1)/2] do
          for l in [0..(r - 1)/2] do
            Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^(Int(c^k)))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
          od;
        od;
      fi;
      if (p - 1) mod (q*r) =0 and q > 2 then
        for k in [1..(q-3)/2] do
          for l in [(r+1)/2..(r-2)] do
            Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Int(rootpq^(Int(c^k)))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
          od;
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q = 2 then
        for l in [0..(r-1)/2] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [3, 2, [3, Rootpr]], [4, 1, [4, Rootpq]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q = 2 then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
        Add(l3, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Rootpr]], [4, 1, [3, 1]], [4, 2, [4, Int(b^((1 - p)/r))]] ]);
      fi;
      if (p + 1) mod (q*r) = 0 and q > 2 then ## qr | (p + 1), q > 2, and G \cong C_{qr} \ltimes C_p^2
        Add(l3, [ [q, r, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matqr[1][1]), 4, Int(matqr[2][1])]],
        [4, 1, [3, Int(matqr[1][2]), 4, Int(matqr[2][2])]],
        [3, 2, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
        [4, 2, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ]);
      fi;
      if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong C_{qr} \ltimes C_p^2
        Add(l3, [ [q, r, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]],
        [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
        [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
      fi;
      if (p + 1) mod (q*r) = 0 and q = 2 then ## qr | (p + 1), q = 2, and G \cong (C_q \ltimes C_r)\ltimes C_p^2
        Add(l3, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [4, 1, [3, 1]],
        [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
        [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
      fi;
      if (p + 1) mod r = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (p - 1), r | (p + 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        Add(l3, [ [q, r, p, p], [3, 1, [3, Rootpq]], [4, 1, [4, Rootpq]],
        [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
        [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
      fi;
      if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        Add(l3, [ [q, r, p, p],
        [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
        [3, 2, [3, Rootpr]], [4, 2, [4, Rootpr]] ]);
      fi;
      data := l3[i - 2 - c1 - c2];
      return SOTRec.groupFromData(data);
    fi;

############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    if i > (2 + c1 + c2 + c3) and i < (3 + c1 + c2 + c3 + c4) then
      l4 := [];
      if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
        Add(l4, [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ]);
      fi;
      if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
        Add(l4, [ [r, p, p, q], [2, 1, [2, Rootpr]] ]);
      fi;
      if (p - 1) mod r = 0 and r > 2 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
        for k in [0..(r - 1)/2] do
         Add(l4, [ [r, p, p, q], [2, 1, [2, Rootpr]], [3, 1, [3, Int(rootpr^(Int(a^k)))]] ]);
        od;
      fi;
      if (p + 1) mod r = 0 and r > 2 then ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
        Add(l4, [ [r, p, p, q],
        [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
        [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ]);
      fi;
      data := l4[i - 2 - c1 - c2 - c3];
      return SOTRec.groupFromData(data);
    fi;

############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    if i > (2 + c1 + c2 + c3 + c4) and i < (3 + c1 + c2 + c3 + c4 + c5) then
      l5 := [];
      if (r - 1) mod q = 0 then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
        Add(l5, [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Rootrq]] ]);
      fi;
      if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
        Add(l5, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
      fi;
      if (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
        for k in [1..(q-1)] do
          Add(l5, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(rootrq^k)]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
        Add(l5, [ [q, p, p, r], [2, 1, [2, Rootpq]] ]);
      fi;
      if (p - 1) mod q = 0 and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
        for k in [0..(q - 1)/2] do
         Add(l5, [ [q, p, p, r], [2, 1, [2, Rootpq]], [3, 1, [3, Int(rootpq^(Int(c^k)))]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 and q = 2 then
        Add(l5, [ [q, p, p, r], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ]);
      fi;
      if (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
        Add(l5, [ [q, r, p, p], [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]], [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
      fi;
      if (r - 1) mod q = 0 then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
        Add(l5, [ [q, r, p, p], [2, 1, [2, Rootrq]] ]);
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
        for k in [1..q-1] do
          Add(l5, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Int(rootpq^k)]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
        for k in [0..(q - 3)/2] do
          Add(l5, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        for l in [1..(q - 3)/2] do
          for k in [0..(q - 1)/2] do
              Add(l5, [ [q, r, p, p], [2, 1, [2, Int(rootrq^(Int(c^l)))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
          od;
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^((1-r)/q))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(b^((1-p)/q))]] ]);
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        for l in [(q - 1)/2..q - 2] do
          for k in [0..(q - 3)/2] do
            Add(l5, [ [q, r, p, p], [2, 1, [2, Int(rootrq^(Int(c^l)))]], [3, 1, [3, Rootpq]], [4, 1, [4, Int(rootpq^(Int(c^k)))]] ]);
          od;
        od;
      fi;
      if q = 2 then ##C_q \ltimes (C_r \times C_p^2)
        Add(l5, [ [q, r, p, p], [2, 1, [2, r - 1]], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ]);
      fi;
      if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
        for k in [1..(q - 1)/2] do
          mat_k := matq^k;
          Add(l5, [ [q, r, p, p], [2, 1, [2, Rootrq]], [3, 1, [3, Int(mat_k[1][1]), 4, Int(mat_k[2][1])]], [4, 1, [3, Int(mat_k[1][2]), 4, Int(mat_k[2][2])]] ]);
        od;
      fi;
      data := l5[i - 2 - c1 - c2 - c3 - c4];
      return SOTRec.groupFromData(data);
    fi;

############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    if i > (2 + c1 + c2 + c3 + c4 + c5) and i < (3 + c1 + c2 + c3 + c4 + c5 + c6) then
      l6 := [];
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
        Add(l6, [ [p, q, p, r], [4, 1, [4, Rootrp]], [4, 2, [4, Rootrq]] ]);
      fi;
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
        Add(l6, [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Rootrp]], [4, 2, [4, Rootrq]] ]);
      fi;
      if (r - 1) mod p = 0 and (p - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
        Add(l6, [ [p, r, q, p], [2, 1, [2, Rootrp]], [4, 3, [4, Rootpq]] ]);
      fi;
      if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
        for k in [1..q-1] do
          Add(l6, [ [p, q, r, p], [3, 1, [3, Rootrp]], [3, 2, [3, Rootrq]], [4, 2, [4, Int(rootpq^k)]] ]);
        od;
      fi;
      data := l6[i - 2 - c1 - c2 - c3 - c4 - c5];
      return SOTRec.groupFromData(data);
    fi;

############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if i > (2 + c1 + c2 + c3 + c4 + c5 + c6) and i < (3 + c1 + c2 + c3 + c4 + c5 + c6 + c7) then
      l7 := [];
      if (r - 1) mod p = 0 then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
        Add(l7, [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Rootrp]] ]);
      fi;
      if (q - 1) mod p = 0 then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
        Add(l7, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]] ]);
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l7, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
        od;
      fi;

      if (r - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
        Add(l7, [ [p, p, q, r], [4, 1, [4, Rootrp]] ]);
      fi;
      if (q - 1) mod p = 0 then ## P \cong C_p^2, p | (q - 1) and G \cong C_p \times (C_p \ltimes C_q) \times C_r
        Add(l7, [ [p, p, q, r], [3, 1, [3, Rootqp]] ]);
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_p^2 and G \cong C_p^2 \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l7, [ [p, p, q, r], [3, 1, [3, Rootqp]], [4, 1, [4, Int(rootrp^k)]] ]);
        od;
      fi;
      data := l7[i - 2 - c1 - c2 - c3 - c4 - c5 - c6];
      return SOTRec.groupFromData(data);
    fi;

############
    if p = 2 and q = 3 and r = 5 and i = 13 then
      return AlternatingGroup(5);
    fi;
############

end;
