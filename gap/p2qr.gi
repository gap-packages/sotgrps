msg.allGroupsP2QR := function(n)
local fac, primefac, p, q, r, a, b, c, u, v, ii, qq, iii, qqq, k, l, matq, matr, matqr, mat, mat_k, all, list;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 3 then
      Error("Argument must be of the form of p^2qr");
    fi;
    primefac := function(n)
      local i, j, tmp;
        tmp := [];
        for i in Collected(fac) do
          if i[2] = 2 then j := i[1];
          elif i[2] = 1 then Add(tmp, i[1]);
          fi;
        od;
        Sort(tmp);
        Add(tmp, j);
      return tmp;
    end;
    p := primefac(n)[3]; q := primefac(n)[1]; r := primefac(n)[2];
    if r = 2 then
      Error("r must be a prime greater than q");
    fi;
    a := Z(r);
    b := Z(p);
    c := Z(q);

    u := ZmodnZObj(Int(Z(p)), p^2);
    if not u^(p-1) = ZmodnZObj(1, p^2) then v := u;
    else v := u + 1;
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
      matqr := msg.QthRootGL2P(p, (q*r));
      mat := matqr^q;
    fi;
    if (p + 1) mod r = 0 and r > 2 then
      matr := msg.QthRootGL2P(p, r);
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      matq := msg.QthRootGL2P(p, q);
    fi;
############ add abelian groups in:
    all := [ [ [p, p, q, r], [1, [2, 1]] ], [ [p, p, q, r] ] ];
############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
    if (r - 1) mod (p^2*q) = 0 then ##C_{p^2q} \ltimes C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(a^((r-1)/(p^2*q)))]], [4, 2, [4, Int(a^((r-1)/(p*q)))]], [4, 3, [4, Int(a^((r-1)/q))]] ]);
    fi;

############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or p | (q - 1)(r - 1)
    if (q - 1) mod (p^2) = 0 then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;
    if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in msg.groupofunitsP2(p) do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/(p^2)))]], [4, 2, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;
    if (r - 1) mod (p^2) = 0 then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Int(a^((r-1)/(p^2)))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
    fi;
    if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1]
        do Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/(p^2)))]], [4, 2, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
      Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
    fi;

############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^((p-1)/r))]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]] ]);
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(q - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(k*(p-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [1..(r - 1)] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 2, [4, Int(b^(k*(p-1)/r))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q > 2 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
      for k in [0..(q - 1)/2] do
        for l in [0..(r - 1)/2] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p - 1) mod (q*r) =0 and q > 2 then
      for k in [1..(q-3)/2] do
        for l in [(r+1)/2..(r-1)] do
          Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then
      for l in [0..(r-1)/2] do
        Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
      od;
    fi;
    if (p - 1) mod (q*r) = 0 and q = 2 then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [3, 1]], [4, 2, [4, Int(b^((1 - p)/r))]] ]);
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
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(b^((p - 1)/q))]], [4, 1, [4, Int(b^((p - 1)/q))]],
      [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
      [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
    fi;
    if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
      Add(all, [ [q, r, p, p],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
      [3, 2, [3, Int(b^((p - 1)/r))]], [4, 2, [4, Int(b^((p - 1)/r))]] ]);
    fi;

############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
      Add(all, [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ]);
    fi;
    if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
      Add(all, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]] ]);
    fi;
    if (p - 1) mod r = 0 and r > 2 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      for k in [0..(r - 1)/2] do
       Add(all, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]], [3, 1, [3, Int(b^(Int(a^k)*(p-1)/r))]] ]);
      od;
    fi;
    if (p + 1) mod r = 0 and r > 2 then ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
      Add(all, [ [r, p, p, q],
      [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
      [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ]);
    fi;

############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    if (r - 1) mod q = 0 then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
      Add(all, [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Int(a^((r-1)/q))]] ]);
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
      Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
    fi;
    if (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
      for k in [1..(q-1)] do
        Add(all, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(a^(k*(r-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
      Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]] ]);
    fi;
    if (p - 1) mod q = 0 and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
      for k in [0..(q - 1)/2] do
       Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int(c^k)*(p-1)/q))]] ]);
      od;
    fi;
    if (p - 1) mod q = 0 and q = 2 then
      Add(all, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int((p-1)/q)))]] ]);
    fi;
    if (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
      Add(all, [ [q, r, p, p], [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]], [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
    fi;
    if (r - 1) mod q = 0 then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
      for k in [1..q-1] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r-1)/q))]], [3, 1, [3, Int(b^(k*(p-1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [0..(q - 3)/2] do
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [1..(q - 3)/2] do
        for k in [0..(q - 1)/2] do
            Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      od;
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^((q - 1)/2))*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^((q - 1)/2))*(p-1)/q))]] ]);
    fi;
    if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
      for l in [(q - 1)/2..q - 2] do
        for k in [0..(q - 3)/2] do
          Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      od;
    fi;
    if q = 2 then
      Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^((p-1)/q))]] ]);
    fi;
    if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
      for k in [1..(q-1)/2] do
        mat_k := matq^k;
        Add(all, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]], [3, 1, [3, Int(mat_k[1][1]), 4, Int(mat_k[2][1])]], [4, 1, [3, Int(mat_k[1][2]), 4, Int(mat_k[2][2])]] ]);
      od;
    fi;

############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
      Add(all, [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
      Add(all, [ [p, r, q, p], [2, 1, [2, Int(a^((r-1)/p))]], [4, 3, [4, Int(b^((p-1)/q))]] ]);
    fi;
    if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
      for k in [1..q-1] do
        Add(all, [ [p, q, r, p], [3, 1, [3, Int(a^((r-1)/p))]], [3, 2, [3, Int(a^((r-1)/q))]], [4, 2, [4, Int(b^(k*(p-1)/q))]] ]);
      od;
    fi;

############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if (r - 1) mod p = 0 then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
      Add(all, [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Int(a^((r-1)/p))]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
      Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;

    if (r - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
      Add(all, [ [p, p, q, r], [4, 1, [4, Int(a^((r-1)/p))]] ]);
    fi;
    if (q - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_r
      Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]] ]);
    fi;
    if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_p^2 and G \cong C_p^2 \ltimes (C_q \times C_r)
      for k in [1..p-1] do
        Add(all, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
      od;
    fi;

############
    list := List(all, x->msg.groupFromData(x));
    if n = 60 then
      Add(list, AlternatingGroup(5));
    fi;
  return list;
end;

######################################################
msg.NumberGroupsP2QR := function(n)
  local s, fac, primefac, p, q, r, m;
    s := [];
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 3 then
      Error("Argument must be of the form of p^2qr"); fi;
      primefac := function(n)
        local i, j, tmp;
          tmp := [];
          for i in Collected(fac) do
            if i[2] = 2 then j := i[1];
            elif i[2] = 1 then Add(tmp, i[1]);
            fi;
          od;
          Sort(tmp);
          Add(tmp, j);
          return tmp;
        end;
    p := primefac(n)[3]; q := primefac(n)[1]; r := primefac(n)[2];

    if n = 60 then m := 13;
    fi;
    if q = 2 then
      m := 10 + (2*r + 7)*msg.deltaDivisibility((p - 1), r) + 3*msg.deltaDivisibility((p + 1), r) + 6*msg.deltaDivisibility((r - 1), p) + 2*msg.deltaDivisibility((r - 1), (p^2));
    fi;
    if q > 2 and not n = 60 then
      m := 2 + (p^2 - p)*msg.deltaDivisibility((q - 1), (p^2))*msg.deltaDivisibility((r - 1), (p^2))
      + (p - 1)*(msg.deltaDivisibility((q - 1), (p^2))*msg.deltaDivisibility((r - 1), p) + msg.deltaDivisibility((r - 1), (p^2))*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p))
      + (q - 1)*(q + 4)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)/2
      + (q - 1)*(msg.deltaDivisibility((p + 1), q)*msg.deltaDivisibility((r - 1), q) + msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((p - 1), (q*r)) + 2*msg.deltaDivisibility((r - 1), (p*q))*msg.deltaDivisibility((p - 1), q))/2
      + (q*r + 1)*msg.deltaDivisibility((p - 1), (q*r))/2
      + (r + 5)*msg.deltaDivisibility((p - 1), r)*(1 + msg.deltaDivisibility((p - 1), q))/2
      + msg.deltaDivisibility((p^2 - 1), (q*r)) + 2*msg.deltaDivisibility((r - 1), (p*q)) + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((p - 1), q) + msg.deltaDivisibility((r - 1), (p^2*q))
      + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p) + 2*msg.deltaDivisibility((q - 1), p) + 3*msg.deltaDivisibility((p - 1), q) + 2*msg.deltaDivisibility((r - 1), p)
      + 2*msg.deltaDivisibility((r - 1), q) + msg.deltaDivisibility((r - 1), (p^2)) + msg.deltaDivisibility((q - 1), p^2) + msg.deltaDivisibility((p + 1), r) + msg.deltaDivisibility((p + 1), q);
    fi;
    return m;
  end;
######################################################
msg.GroupP2QR := function(n, i)
  local fac, primefac, p, q, r, a, b, c, u, v, ii, qq, iii, qqq, k, l, matq, matr, matqr, mat, mat_k,
  c1, c2, c3, c4, c5, c6, c7, l1, l2, l3, l4, l5, l6, l7, l0, data, G;
    fac := Factors(n);
    if not Length(fac) = 4 or not Length(Collected(fac)) = 3 then
      Error("Argument must be of the form of p^2qr");
    fi;
    primefac := function(n)
      local i, j, tmp;
        tmp := [];
        for i in Collected(fac) do
          if i[2] = 2 then j := i[1];
          elif i[2] = 1 then Add(tmp, i[1]);
          fi;
        od;
        Sort(tmp);
        Add(tmp, j);
      return tmp;
    end;
    p := primefac(n)[3]; q := primefac(n)[1]; r := primefac(n)[2];
    if r = 2 then
      Error("r must be a prime greater than q");
    fi;
    a := Z(r);
    b := Z(p);
    c := Z(q);

    u := ZmodnZObj(Int(Z(p)), p^2);
    if not u^(p-1) = ZmodnZObj(1, p^2) then v := u;
    else v := u + 1;
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
      matqr := msg.QthRootGL2P(p, (q*r));
      mat := matqr^q;
    fi;
    if (p + 1) mod r = 0 and r > 2 then
      matr := msg.QthRootGL2P(p, r);
    fi;
    if (p + 1) mod q = 0 and q > 2 then
      matq := msg.QthRootGL2P(p, q);
    fi;
############ enumeration of distinct cases
    c1 := msg.deltaDivisibility((r - 1), p^2*q);;
    c2 := msg.deltaDivisibility((q - 1), p^2) + (p - 1)*msg.deltaDivisibility((q - 1), p^2)*msg.deltaDivisibility((r - 1), p)
    + (p^2 - p)*msg.deltaDivisibility((r - 1), p^2)*msg.deltaDivisibility((q - 1), p^2)
    + msg.deltaDivisibility((r - 1), p^2) + (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p^2)
    + msg.deltaDivisibility((r - 1), p)*msg.deltaDivisibility((q - 1), p);;
    c3 := 1/2*(q*r+q+r+7)*msg.deltaDivisibility((p - 1), q*r)
    + msg.deltaDivisibility((p^2 - 1), q*r)*(1 - msg.deltaDivisibility((p - 1), q*r))*(1 - msg.deltafunction(q, 2))
    + 2*msg.deltaDivisibility((p + 1), r)*msg.deltafunction(q, 2);;
    c4 := 1/2*(r + 5)*msg.deltaDivisibility((p - 1), r) + msg.deltaDivisibility((p + 1), r);;
    c5 := 8*msg.deltafunction(q, 2)
    + (1 - msg.deltafunction(q, 2))*(1/2*(q - 1)*(q + 4)*msg.deltaDivisibility((p - 1), q)*msg.deltaDivisibility((r - 1), q)
    + 1/2*(q - 1)*msg.deltaDivisibility((p + 1), q)*msg.deltaDivisibility((r - 1), q)
    + 1/2*(q + 5)*msg.deltaDivisibility((p - 1), q)
    + 2*msg.deltaDivisibility((r - 1), q)
    + msg.deltaDivisibility((p + 1), q));;
    c6 := msg.deltaDivisibility((r - 1), p)*(msg.deltaDivisibility((p - 1), q)*(1 + (q - 1)*msg.deltaDivisibility((r - 1), q))
    + 2*msg.deltaDivisibility((r - 1), q));;
    c7 := 2*(msg.deltaDivisibility((q - 1), p) + msg.deltaDivisibility((r - 1), p) +
    (p - 1)*msg.deltaDivisibility((q - 1), p)*msg.deltaDivisibility((r - 1), p));

############ add abelian groups in:
    l0 := [ [ [p, p, q, r], [1, [2, 1]] ], [ [p, p, q, r] ] ];
    if i < 3 then G := msg.groupFromData(l0[i]);
      return G;
    fi;
############ case 1: nonabelian and Fitting subgroup has order r -- unique isomorphism type iff p^2q | (r - 1)
    if (r - 1) mod (p^2*q) = 0 and i > 2 and i < (3 + c1) then ##C_{p^2q} \ltimes C_r
      l1 := [];
      Add(l1, [ [p, p, q, r], [1, [2, 1]], [2, [3, 1]], [4, 1, [4, Int(a^((r-1)/(p^2*q)))]], [4, 2, [4, Int(a^((r-1)/(p*q)))]], [4, 3, [4, Int(a^((r-1)/q))]] ]);
      data := l1[i - 2];
      return msg.groupFromData(data);
    fi;

############ case 2: nonabelian and Fitting subgroup has order qr -- p^2 | (q - 1)(r - 1) or (p^2 | (q - 1) or (r - 1)) or (p | (q - 1) and p | (r - 1))
    if i > (2 + c1) and i < (3 + c1 + c2) then
      l2 := [];
      if (q - 1) mod (p^2) = 0 then ## p^2 | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
        Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]] ]);
      fi;
      if (q - 1) mod (p^2) = 0 and (r - 1) mod p = 0 then ## p^2 | (q - 1), p | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
        od;
      fi;
      if (q - 1) mod (p^2) = 0 and (r - 1) mod (p^2) = 0 then ## p^2 | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in msg.groupofunitsP2(p) do
          Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/(p^2)))]], [3, 2, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/(p^2)))]], [4, 2, [4, Int(a^(k*(r-1)/p))]] ]);
        od;
      fi;
      if (r - 1) mod (p^2) = 0 then ## p^2 | (r - 1), and G \cong (C_{p^2} \ltimes C_r) \times C_q
        Add(l2, [ [p, p, q, r], [1, [2, 1]], [4, 1, [4, Int(a^((r-1)/(p^2)))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
      fi;
      if (r - 1) mod (p^2) = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p^2 | (r - 1), and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1]
          do Add(l2, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/(p^2)))]], [4, 2, [4, Int(a^(k*(r-1)/p))]] ]);
        od;
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## p | (q - 1), p | (r - 1), and G \cong (C_p \ltimes C_q) \times (C_p \ltimes C_r)
        Add(l2, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 2, [4, Int(a^((r-1)/p))]] ]);
      fi;
      data := l2[i - 2 - c1];
      return msg.groupFromData(data);
    fi;

############ case 3: nonabelian and Fitting subgroup has order p^2 -- qr | (p^2 - 1)
    if i > (2 + c1 + c2) and i < (3 + c1 + c2 + c3) then
      l3 := [];
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_{p^2}
        Add(l3, [ [q, r, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [3, 2, [3, iii, 4, qqq]], [4, 1, [4, ii]], [4, 2, [4, iii]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_q \ltimes C_p) \times (C_r \ltimes C_p)
        Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^((p-1)/r))]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong (C_{qr} \ltimes C_p) \times C_p
        Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]] ]);
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [1..(q - 1)] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(k*(p-1)/q))]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [1..(r - 1)] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 2, [4, Int(b^(k*(p-1)/r))]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q > 2 then ## qr | (p - 1) and G \cong C_{qr} \ltimes C_p^2
        for k in [0..(q - 1)/2] do
          for l in [0..(r - 1)/2] do
            Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
          od;
        od;
      fi;
      if (p - 1) mod (q*r) =0 and q > 2 then
        for k in [1..(q-3)/2] do
          for l in [(r+1)/2..(r-1)] do
            Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
          od;
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q = 2 then
        for l in [0..(r-1)/2] do
          Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p-1)/q))]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [4, Int(b^((p-1)/q))]], [4, 2, [4, Int(b^(Int(a^l)*(p-1)/r))]] ]);
        od;
      fi;
      if (p - 1) mod (q*r) = 0 and q = 2 then ##q = 2, r | (p - 1), and G \cong (C_2 \ltimes C_r) \ltimes C_p^2
        Add(l3, [ [q, r, p, p], [2, 1, [2, r-1]], [3, 1, [4, 1]], [3, 2, [3, Int(b^((p-1)/r))]], [4, 1, [3, 1]], [4, 2, [4, Int(b^((1 - p)/r))]] ]);
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
        Add(l3, [ [q, r, p, p], [3, 1, [3, Int(b^((p - 1)/q))]], [4, 1, [4, Int(b^((p - 1)/q))]],
        [3, 2, [3, Int(matr[1][1]), 4, Int(matr[2][1])]],
        [4, 2, [3, Int(matr[1][2]), 4, Int(matr[2][2])]] ]);
      fi;
      if (p - 1) mod r = 0 and (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), r | (p - 1), and G \cong (C_q \times C_r) \ltimes C_p^2
        Add(l3, [ [q, r, p, p],
        [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]],
        [3, 2, [3, Int(b^((p - 1)/r))]], [4, 2, [4, Int(b^((p - 1)/r))]] ]);
      fi;
      data := l3[i - 2 - c1 - c2];
      return msg.groupFromData(data);
    fi;

############ case 4: nonabelian and Fitting subgroup has order p^2q -- r | (p - 1) or r | (p + 1)
    if i > (2 + c1 + c2 + c3) and i < (3 + c1 + c2 + c3 + c4) then
      l4 := [];
      if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_{p^2}) \times C_q
        Add(l4, [ [r, p, p, q], [2, [3, 1]], [2, 1, [2, iii, 3, qqq]], [3, 1, [3, iii]] ]);
      fi;
      if (p - 1) mod r = 0 then ## r | (p - 1) and G \cong (C_r \ltimes C_p) \times (C_p \times C_q)
        Add(l4, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]] ]);
      fi;
      if (p - 1) mod r = 0 and r > 2 then ## r | (p - 1) and G \cong (C_r \ltimes C_p^2) \times C_q
        for k in [0..(r - 1)/2] do
         Add(l4, [ [r, p, p, q], [2, 1, [2, Int(b^((p-1)/r))]], [3, 1, [3, Int(b^(Int(a^k)*(p-1)/r))]] ]);
        od;
      fi;
      if (p + 1) mod r = 0 and r > 2 then ## r | (p + 1) and G \cong (C_r \ltimes C_p^2) \times C_q
        Add(l4, [ [r, p, p, q],
        [2, 1, [2, Int(matr[1][1]), 3, Int(matr[2][1])]],
        [3, 1, [2, Int(matr[1][2]), 3, Int(matr[2][2])]] ]);
      fi;
      data := l4[i - 2 - c1 - c2 - c3];
      return msg.groupFromData(data);
    fi;

############ case 5: nonabelian and Fitting subgroup has order p^2r -- q | (p - 1)(r - 1) or q | (p + 1)(r - 1)
    if i > (2 + c1 + c2 + c3 + c4) and i < (3 + c1 + c2 + c3 + c4 + c5) then
      l5 := [];
      if (r - 1) mod q = 0 then ## q \mid (r - 1) and G \cong (C_q \ltimes C_r) \times C_{p^2}
        Add(l5, [ [q, r, p, p], [3, [4, 1]], [2, 1, [2, Int(a^((r-1)/q))]] ]);
      fi;
      if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_{p^2}) \times C_r
        Add(l5, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ]);
      fi;
      if (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q \mid (p - 1) and G \cong C_q \ltimes (C_{p^2} \times C_r)
        for k in [1..(q-1)] do
          Add(l5, [ [q, p, p, r], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]], [4, 1, [4, Int(a^(k*(r-1)/q))]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 then ## q \mid (p - 1) and G \cong (C_q \ltimes C_p) \times C_p \times C_r
        Add(l5, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]] ]);
      fi;
      if (p - 1) mod q = 0 and q > 2 then ## q | (p - 1) and G \cong (C_q \ltimes C_p^2) \times C_r
        for k in [0..(q - 1)/2] do
         Add(l5, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      fi;
      if (p - 1) mod q = 0 and q = 2 then
        Add(l5, [ [q, p, p, r], [2, 1, [2, Int(b^((p-1)/q))]], [3, 1, [3, Int(b^(Int((p-1)/q)))]] ]);
      fi;
      if (p + 1) mod q = 0 and q > 2 then ## q | (p + 1), and G \cong (C_q \ltimes C_p^2) \times C_r
        Add(l5, [ [q, r, p, p], [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]], [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
      fi;
      if (r - 1) mod q = 0 then ## q | (r - 1), and G \cong (C_q \ltimes C_r) \times C_p^2
        Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]] ]);
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p) \times C_p
        for k in [1..q-1] do
          Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^((r-1)/q))]], [3, 1, [3, Int(b^(k*(p-1)/q))]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p - 1), and G \cong C_q \ltimes (C_r \times C_p^2)
        for k in [0..(q - 3)/2] do
          Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^((r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        for l in [1..(q - 3)/2] do
          for k in [0..(q - 1)/2] do
              Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
          od;
        od;
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^((q - 1)/2))*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^((q - 1)/2))*(p-1)/q))]] ]);
      fi;
      if (r - 1) mod q = 0 and (p - 1) mod q = 0 and q > 2 then
        for l in [(q - 1)/2..q - 2] do
          for k in [0..(q - 3)/2] do
            Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c^l)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^(Int(c^k)*(p-1)/q))]] ]);
          od;
        od;
      fi;
      if q = 2 then ##C_q \ltimes (C_r \times C_p^2)
        Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^(Int(c)*(r-1)/q))]], [3, 1, [3, Int(b^((p-1)/q))]], [4, 1, [4, Int(b^((p-1)/q))]] ]);
      fi;
      if (p + 1) mod q = 0 and (r - 1) mod q = 0 and q > 2 then ## q | (r - 1), q | (p + 1), and G \cong C_q \ltimes (C_r \times C_p^2)
        for k in [1..(q - 1)/2] do
          mat_k := matq^k;
          Add(l5, [ [q, r, p, p], [2, 1, [2, Int(a^((r - 1)/q))]], [3, 1, [3, Int(mat_k[1][1]), 4, Int(mat_k[2][1])]], [4, 1, [3, Int(mat_k[1][2]), 4, Int(mat_k[2][2])]] ]);
        od;
      fi;
      data := l5[i - 2 - c1 - c2 - c3 - c4];
      return msg.groupFromData(data);
    fi;

############ case 6: nonabelian and Fitting subgroup has order pr -- q | (p - 1)(r - 1) and p | (r - 1)
    if i > (2 + c1 + c2 + c3 + c4 + c5) and i < (3 + c1 + c2 + c3 + c4 + c5 + c6) then
      l6 := [];
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
        Add(l6, [ [p, q, p, r], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
      fi;
      if (r - 1) mod p = 0 and (r - 1) mod q = 0 then ## q | (r - 1), p | (r - 1), and G \cong (C_p \times C_q) \ltimes C_r \times C_p
        Add(l6, [ [p, q, p, r], [1, [3, 1]], [4, 1, [4, Int(a^((r-1)/p))]], [4, 2, [4, Int(a^((r-1)/q))]] ]);
      fi;
      if (r - 1) mod p = 0 and (p - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), and G \cong (C_p \ltimes C_r) \times (C_q \ltimes C_p)
        Add(l6, [ [p, r, q, p], [2, 1, [2, Int(a^((r-1)/p))]], [4, 3, [4, Int(b^((p-1)/q))]] ]);
      fi;
      if (r - 1) mod p = 0 and (p - 1) mod q = 0 and (r - 1) mod q = 0 then ## q | (p - 1), p | (r - 1), q | (r - 1), and G \cong (C_p \times C_q) \ltimes (C_r \times C_p)
        for k in [1..q-1] do
          Add(l6, [ [p, q, r, p], [3, 1, [3, Int(a^((r-1)/p))]], [3, 2, [3, Int(a^((r-1)/q))]], [4, 2, [4, Int(b^(k*(p-1)/q))]] ]);
        od;
      fi;
      data := l6[i - 2 - c1 - c2 - c3 - c4 - c5];
      return msg.groupFromData(data);
    fi;

############ case 7: nonabelian and Fitting subgroup has order pqr -- p | (r - 1)(q - 1)
    if i > (2 + c1 + c2 + c3 + c4 + c5 + c6) and i < (3 + c1 + c2 + c3 + c4 + c5 + c6 + c7) then
      l7 := [];
      if (r - 1) mod p = 0 then ## P \cong C_{p^2}, p | (r - 1) and G \cong (C_{p^2} \ltimes C_r) \times C_q
        Add(l7, [ [p, p, r, q], [1, [2, 1]], [3, 1, [3, Int(a^((r-1)/p))]] ]);
      fi;
      if (q - 1) mod p = 0 then ## P \cong C_{p^2}, p | (q - 1) and G \cong (C_{p^2} \ltimes C_q) \times C_r
        Add(l7, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]] ]);
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_{p^2} and G \cong C_{p^2} \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l7, [ [p, p, q, r], [1, [2, 1]], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
        od;
      fi;

      if (r - 1) mod p = 0 then ## P \cong C_p^2, p | (r - 1) and G \cong C_p \times (C_p \ltimes C_r) \times C_q
        Add(l7, [ [p, p, q, r], [4, 1, [4, Int(a^((r-1)/p))]] ]);
      fi;
      if (q - 1) mod p = 0 then ## P \cong C_p^2, p | (q - 1) and G \cong C_p \times (C_p \ltimes C_q) \times C_r
        Add(l7, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]] ]);
      fi;
      if (r - 1) mod p = 0 and (q - 1) mod p = 0 then ## P \cong C_p^2 and G \cong C_p^2 \ltimes (C_q \times C_r)
        for k in [1..p-1] do
          Add(l7, [ [p, p, q, r], [3, 1, [3, Int(c^((q-1)/p))]], [4, 1, [4, Int(a^(k*(r-1)/p))]] ]);
        od;
      fi;
      data := l7[i - 2 - c1 - c2 - c3 - c4 - c5 - c6];
      return msg.groupFromData(data);
    fi;

############
    if n = 60 and i = 13 then
      return AlternatingGroup(5);
    fi;
############

end;
