## Construct all groups of order p^4q: all such groups are solvable.
## The isomorphism types of nilpotent groups of such order are in one-to-one correspondence with the isomorphism type of the Sylow p-subgroup. In particular, such groups are stored by "lowpowerPGroups".
## It remains to investigate the non-nilpotent groups. There are three classes of such groups: one class where the Sylow p-subgroup is normal, one where the Sylow q-subgroup is normal, and one with no normal Sylow subgroups.
## Note that two split extensions C_q \ltimes_\phi P and C_q \ltimes_\psi P are isomorphic if and only if Im(\phi) and Im(\psi) are conjugate in Aut(P) (see [2, Proposition 3.6]).
  ## Moreover, we apply the following result (Lemma 9 in The enumeration of groups of order p^nq for n ≤ 5 by Eick & Moede):
  ## Theorem:
  ## Let p, q be distinct primes and let G, H be finite groups. If there exists a homomorphism \phi : G \to H such that Ker(\phi) is a p-group, then the number of conjugacy classes of subgroups of order q in G and in H coincide.

## This implies that if G is a finite group. Recall that O_p(G) (PCore(G) in GAP) is the largest normal p-subgroup of G. The natural projection \pi : G \to O_p(G) thus is a homomorphism with p-group kernel. It then follows that the number of conjugacy classes of subgroups of order q in G coincides with that in G/O_p(G).
  ## In particular, setting G \cong Aut(P), this shows that the number of isomorphism types of C_q \ltimes P for a given p-group P coincides with the number of conjugacy classes of subgroups of order q in Aut(P)/O_p(Aut(P)).
###################################################################
SOTRec.allGroupsP4Q := function(p, q, arg...)
  local all, list, a, b, c, d, e, f, g, h, r1, r2, r3, r4, s1, s2, s3, s4, u, v, w, x, y,
        R1, R2, R3, R4, S1, S2, S3, S4, mat, matGL2, matGL3, matGL4, func, funci, i, j, k, l, m;
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    a := Z(p);
    b := Z(q);
    if (q - 1) mod p = 0 then
      r1 := b^((q-1)/p);
      R1 := Int(r1);
    fi;
    if (q - 1) mod (p^2) = 0 then
      r2 := b^((q-1)/(p^2));
      R2 := Int(r2);
    fi;
    if (q - 1) mod (p^3) = 0 then
      r3 := b^((q-1)/(p^3));
      R3 := Int(r3);
    fi;
    if (q - 1) mod (p^4) = 0 then
      r4 := b^((q-1)/(p^4));
      R4 := Int(r4);
    fi;
    if (p - 1) mod q = 0 then
      if not Int(a)^(p - 1) mod p^2 = 1 then
        c := ZmodnZObj(Int(a), p^2);
        d := ZmodnZObj(Int(a), p^3);
        e := ZmodnZObj(Int(a), p^4);
      else
        c := ZmodnZObj(Int(a) + p, p^2);
        d := ZmodnZObj(Int(a) + p, p^3);
        e := ZmodnZObj(Int(a) + p, p^4);
      fi;
      s1 := a^((p - 1)/q);;
      s2 := c^((p^2 - p)/q);;
      s3 := d^((p^3 - p^2)/q);;
      s4 := e^((p^4 - p^3)/q);;
      S1 := Int(s1);;
      S2 := Int(s2);;
      S3 := Int(s3);;
      S4 := Int(s4);;
    fi;
    ##construct all nilpotent groups:
    all := [];
    for i in SOTRec.lowpowerPGroups(p, 4, 0) do
      Add(i[1], q);
      Add(all, i);
    od;

    ##Class 1: Group G is solvable, nonnilpotent. Sylow p-subgroup is normal in G. Thus G \cong C_q \ltimes P is a nonabelian split extension.
    ##Isomorphism types of such groups are in one-to-one correspondence with the conjugacy classes of cyclic subgroups of order q in \Aut P.

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    #1 P \cong C_{p^4}
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]);
    fi;
    if (q - 1) mod p^2 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]);
    fi;
    if (q - 1) mod p^3 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]);
    fi;
    if (q - 1) mod p^4 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R4]], [5, 2, [5, R3]], [5, 3, [5, R2]], [5, 4, [5, R1]] ]);
    fi;

    #2 P \cong C_{p^3} \times C_p
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 4, [5, R1]] ]); #Z(G) \cong C_{p^3}
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
    fi;
    if (q - 1) mod p^2 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2}
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
    fi;
    if (q - 1) mod p^3 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #Z(G) \cong C_p
    fi;

    #3 P \cong C_{p^2} \times C_{p^2}
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
    fi;
    if (q - 1) mod p^2 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2}
    fi;

    #4 P \cong C_{p^2} \times C_p^2
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 3, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
    fi;
    if (q - 1) mod p^2 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
    fi;

    #5 P \cong C_p^4
    if (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
    fi;

    #6 P \cong [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or P \cong [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong p_- \times C_q
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \ltimes F(G), Z(G) \cong C_4
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong D_4 \times C_q, G \cong C_2 \ltimes (C_4 \ltimes C_q \times C_2), Z(G) \cong C_2
      Add(all, [ [2, 2, 2, 2, q], [2, [4, 1]], [3, [4, 1]], [3, 1, [3, 1, 4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]);#F(G) \cong Q_8 \times C_q, G \cong C_2 \ltimes (Q_8 \ltimes C_q), Z(G) \cong C_2
    fi;

    #7 P \cong [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^3} \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      fi;
      if (q - 1) mod p^2 = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r2^k)]], [5, 2, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^2} \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]);#F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \times D_{4q}
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, q - 1]] ]);#F(G) \cong D_4 \times C_q, G \cong D_q \times D_4
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, q - 1]] ]);#F(G) \cong C_q \times C_2^3, G \cong (D_4 \ltimes C_q) \times C_2
    fi;

    #8 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_- \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \ltimes F(G), Z(G) \cong C_2^2
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_2^3 \times C_q, G \cong C_2 \ltimes (C_2 \ltimes C_q \times C_2^2)
      if (q - 1) mod (p^2) = 0 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_q \times C_2^2, G \cong C_2 \ltimes ((C_4 \ltimes C_q) \times C_2)
      fi;
    fi;

    #9 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times (C_4 \times C_2), G \cong C_2 \times (Q_8 \ltimes C_q)
      Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, q - 1]] ]); #F(G) \cong C_q \times Q_8, G \cong D_q \times Q_8
    fi;

    #10 P \cong [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]);
        for k in [1..p - 1] do #F(G) \cong (C_p \times C_{p^2}) \times C_q
          Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]);
        od;
      fi;
      if (q - 1) mod p^2 = 0 then #F(G) \cong C_{p^2} \times C_q
        for k in [1..p - 1] do
          Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r2^k)]], [5, 4, [5, Int(r1^k)]] ]);
        od;
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times (C_4 \times C_2)
      Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times (C_4 \times C_2)
      if (q - 1) mod (p^2) = 0 then
        Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, R2]], [5, 4, [5, q - 1]] ]); #F(G) \cong C_q \times C_4
      fi;
    fi;

    #11 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times C_4 \times C_2
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [4, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_q \times C_4
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_q \times C_2^2
      fi;
    fi;

    #12 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1,[3, 1, 4, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        for k in [1..(p - 1)/2] do
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        if p > 3 then
          for k in [1..(p - 1)/2] do
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong p_- \times C_q
          od;
        else #p = 3
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, p - 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, p - 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong 3_- \times C_q
        fi;
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times D_4
      Add(all, [ [2, 2, 2, 2, q], [2, [4, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times Q_8
    fi;

    #13 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ]
    if p > 3 and (q - 1) mod p = 0 then
      for k in [1..(p - 1)/2] do
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      od;
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      for k in [1..(p - 1)/2] do
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong p_- \times C_q
      od;
    elif p = 3 and (q - 1) mod 3 = 0 then
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
      Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times D_4
    fi;


    #14 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ]
    if p > 2 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      fi;
      if p = 3 and (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]);
      fi;
    elif p = 2 then
      Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
      Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times Q_8
    fi;

    #15 P \cong [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] if p > 3,
    #or P \cong [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] if p = 3
    if p > 3 and (q - 1) mod p = 0 then
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
      Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
    fi;
    if p = 3 and (q - 1) mod 3 = 0 then
      Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
      Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_- \times C_q
    fi;

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    #1 P \cong C_{p^4}
    if (p - 1) mod q = 0 then
      u := S4 mod p;
      v := (S4 - u)/p mod p;
      x := ((S4 - u)/p - v)/p mod p;
      y := (((S4 - u)/p - v)/p - x)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v, 4, x, 5, y]], [3, 1, [3, u, 4, v, 5, x]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #unique
    fi;

    #2 P \cong C_{p^3} \times C_p
    if (p - 1) mod q = 0 then
      u := S3 mod p;
      v := (S3 - u)/p mod p;
      x := ((S3 - u)/p - v)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_{p^3}
      for k in [1..(q - 1)] do
          Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, Int(s1^k)]] ]); #Z(G) = 1
      od;
    fi;

    #3 P \cong C_{p^2} \times C_{p^2}
    if (p - 1) mod q = 0 then
      u := S2 mod p;
      v := (S2 - u)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]] ]); #Z(G) \cong C_{p^2}
      for k in [0..Int((q - 1)/2)] do
        x := Int(s2^(Int(b^k))) mod p;
        y := (Int(s2^(Int(b^k))) - x)/p;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]], [4, 1, [4, x, 5, y]], [5, 1, [5, x]] ]); #Z(G) = 1
      od;
    elif (p + 1) mod q = 0 and q > 2 then
      mat := SOTRec.QthRootM2P2(p, q);
      Add(all, [ [q, p, p, p, p], [2, [4, 1]], [3, [5, 1]],
      [2, 1, [2, mat[1][1], 3, mat[2][1], 4, mat[3][1], 5, mat[4][1]]],
      [3, 1, [2, mat[1][2], 3, mat[2][2], 4, mat[3][2], 5, mat[4][2]]],
      [4, 1, [2, mat[1][3], 3, mat[2][3], 4, mat[3][3], 5, mat[4][3]]],
      [5, 1, [2, mat[1][4], 3, mat[2][4], 4, mat[3][4], 5, mat[4][4]]] ]);
    fi;

    #4 P \cong C_{p^2} \times C_p^2
    if (p - 1) mod q = 0 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]] ]); #Z(G) \cong C_p \times C_{p^2}
      for k in [0..Int((q - 1)/2)] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]] ]); #Z(G) \cong C_{p^2}
      od;
      Add(all, [ [q, p, p, p, p], [4, [5, 1]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) \cong C_p^2
      for k in [1..(q - 1)] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) \cong C_p
      od;
      #below trivial centre
      for k in [1..(q - 1)] do
        for l in [k + 1..(q - 1)] do;
          Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [3, 1, [3, Int(s1^l)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]);
        od;
      od;
      for k in [1..(q - 1)] do
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [3, 1, [3, Int(s1^k)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]);
      od;
    elif (p + 1) mod q = 0 and q > 2 then
      matGL2 := SOTRec.QthRootGL2P(p, q);
      Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
    fi;

    #5 P \cong C_p^4
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]] ]); #Z(G) \cong C_p^3, G \cong (C_q \ltimes C_p) \times C_p^3
      for k in [0..Int((q - 1)/2)] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^Int(b^k))]] ]); #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
      od;
      #below Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
      if q = 2 then
        Add(all, [ [q, p, p ,p, p], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1)]], [4, 1, [4, (p - 1)]] ]);
      elif q = 3 then
        for k in [0, 1] do
          Add(all, [ [q, p, p ,p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
        od;
      else #q > 3
        for k in [1..(q - 1)] do
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^k)]] ]);
        od;

        func := function(q)
          local qq, res, a,b,c,d,t,bb;
            res :=[];
            qq  := q-1;
            bb  := (q-1) mod 3;
            bb  := (q-1-bb) / 3;
            for a in [1..bb] do
              for b in [2*a..(q-2-a)] do
                t := [[-a,b-a],[-b,a-b]] mod qq;
                if ForAll(t,x-> [a,b] <= SortedList(x))  then
                 Add(res,[a,b]);
                fi;
              od;
            od;
            if (q - 1) mod 3 = 0 then
              Add(res, [bb, 2*bb]);
            fi;
          return res;
        end; #explength := 1/6*(q^2 - 5*q + 6 + 4*SOTRec.w((q - 1), 3));

        for k in func(q) do
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]] ]);
        od;
      fi;
      #below: Z(G) = 1, G \cong C_q \ltimes C_p^4
      for k in [0..(q - 2)] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, S1]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
      od;
      for k in [1..Int((q - 1)/2)] do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
      od;
      for k in [1..(q - 2)] do
        for l in [k + 1..(q - 2)] do
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^l)))]] ]);
        od;
      od;

      funci := function(q)
        local res, a,b,c,d,t;
           res :=[];
           for a in [1..Int((q-1)/4)] do
              for b in [2*a..(q-1)/2] do
                 for c in [b+a..q-2-a] do
                   Add(res,[a,b,c]);
               od;
             od;
             for b in [(q+1)/2..q-1-2*a] do
                for c in [b+a+1..q-2-a] do
                  Add(res,[a,b,c]);
              od;
            od;
           od;
           if (q-1) mod 4 = 0 then
             Add(res, [(q-1)/4, (q-1)/2, 3*(q-1)/4]);
           fi;
           return res;
        end;
      #expected length 1/24*(q^3- 9*q^2+29*q-33 + 12*SOTRec.w((q - 1), 4))
      for k in funci(q) do
        Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]], [5, 1, [5, Int(s1^(Int(b^(k[3]))))]] ]);
      od;
    elif (p + 1) mod q = 0 and q > 2 then #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
      matGL2 := SOTRec.QthRootGL2P(p, q);
      Add(all, [ [q, p, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
      for k in [0..Int((q - 1)/4)] do
        m := matGL2^(Int(b^k));;
        Add(all, [ [q, p, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]],
         [4, 1, [4, Int(m[1][1]), 5, Int(m[2][1])]], [5, 1, [4, Int(m[1][2]), 5, Int(m[2][2])]] ]);
       od;
    elif (p^2 + p + 1) mod q = 0 and q > 3 then #Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
      matGL3 := SOTRec.QthRootGL3P(p, q);
      Add(all, [ [q, p, p, p, p],
      [2, 1, [2, Int(matGL3[1][1]), 3, Int(matGL3[2][1]), 4, Int(matGL3[3][1])]],
      [3, 1, [2, Int(matGL3[1][2]), 3, Int(matGL3[2][2]), 4, Int(matGL3[3][2])]],
      [4, 1, [2, Int(matGL3[1][3]), 3, Int(matGL3[2][3]), 4, Int(matGL3[3][3])]] ]);
    elif (p^2 + 1) mod q = 0 and q > 3 then #Z(G) = 1, G \cong C__q \ltimes C_p^4
      matGL4 := SOTRec.QthRootGL4P(p,q);
      Add(all, [ [q, p, p, p, p],
      [2, 1, [2, Int(matGL4[1][1]), 3, Int(matGL4[2][1]), 4, Int(matGL4[3][1]), 5, Int(matGL4[4][1])]],
      [3, 1, [2, Int(matGL4[1][2]), 3, Int(matGL4[2][2]), 4, Int(matGL4[3][2]), 5, Int(matGL4[4][2])]],
      [4, 1, [2, Int(matGL4[1][3]), 3, Int(matGL4[2][3]), 4, Int(matGL4[3][3]), 5, Int(matGL4[4][3])]],
      [5, 1, [2, Int(matGL4[1][4]), 3, Int(matGL4[2][4]), 4, Int(matGL4[3][4]), 5, Int(matGL4[4][4])]] ]);
    fi;

    #6 P \cong [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [3, [4, 1]], [2, 1, [2, 1, 4, 1]] ]
    if (p - 1) mod q = 0 and p > 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [5, 1, [5, S1]], [2, 1, [2, Int(s1^-1)]] ]); #Z(G) \cong C_{p^2}, G \cong C_q \ltimes (C_p \ltimes (C_p \times C_{p^2}))
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [2, 1, [2, S1]] ]); #Z(G) = 1, |G'| = p^3 , G \cong C_q \ltimes (C_p \ltimes (C_p \ltimes C_{p^2}))
      for k in [2..Int((q + 1)/2)] do #Z(G) = 1, G' = P, G \cong (C_q \ltimes C_p^2) \times C_p^2
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, Int(s1^k)]], [2, 1, [2, Int(s1^(q + 1 - k))]] ]);
      od;
    elif (p + 1) mod q = 0 and q > 2 and p > 2 then
      matGL2 := SOTRec.QthRootGL2P(p, q);
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]],
      [2, 1, [2, Int(matGL2[1][1]), 5, Int(matGL2[2][1])]],
      [5, 1, [2, Int(matGL2[1][2]), 5, Int(matGL2[2][2])]] ]);
    elif p = 2 and q = 3 then
      Add(all, [ [3, 2, 2, 2, 2], [2, [5, 1]], [3, [5, 1]], [4, [5, 1]], [3, 1, [4, 1]], [4, 1, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]] ]);
    fi;

    #7 P \cong [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ]
    if (p - 1) mod q = 0 then
      u := S3 mod p;
      v := (S3 - u)/p mod p;
      x := ((S3 - u)/p - v)/p;
      Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 2, [4, 1, 5, 1]] ]);
    fi;

    #8 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if (p - 1) mod q = 0 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, (C_q \ltimes C_p) \times (C_p \ltimes C_{p^2}), G' \cong C_p^2
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, G \cong (C_q \ltimes (C_p \ltimes C_{p^2})) \times C_p, G' \cong C_{p^2}
      for k in [1..q - 1] do #Z(G) = 1
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, Int(s1^k)]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]);
      od;
    fi;

    #9 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if (p - 1) mod q = 0 and p > 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, S1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, G \cong (C_q \ltimes (C_p \ltimes C_{p^2})) \times C_p, G' \cong C_p^2
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, Int(s1^(-1))]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, C_q \ltimes (C_p \ltimes (C_p \times C_{p^2})), G' \cong P
      for k in [1..q - 2] do
        x := Int(s2^k) mod p;;
        y := (Int(s2^k) - x)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, S1]], [5, 1, [5, Int(s1^(k+1))]], [3, 1, [3, x, 4, y]], [4, 1, [4, x]] ]); #Z(G) = 1, G \cong , G' \cong P
      od;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 1, [5, S1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) = 1, G \cong C_q \ltimes (C_p \ltimes (C_p \times C_{p^2}), G' \cong C_p \times C_{p^2}
    elif p = 2 and q = 3 then
      Add(all, [ [3, 2, 2, 2, 2], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ]); #Z(G) \cong C_2^2
    fi;

    #10 P \cong [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    if (p - 1) mod q = 0 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [2, [5, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, G \cong C_q \ltimes (C_{p^2} \ltimes C_{p^2})
    fi;

    #11 P \cong [ [p, p, p, p], [2, 1, [2, 1, 3, 1]] ] Centre = [f3, f4]; DerivedSubgroup = [f3]
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, Int(s1^(-1))]], [3, 1, [3, S1]] ]); #Z(G) \cong C_p^2, G' \cong C_p^3
      Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, G' \cong C_p^2
      Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [4, 1, [4, S1]] ]); #Z(G) \cong C_p, G' \cong C_p^2
      for k in [2..Int((q + 1)/2)] do #Z(G) \cong C_p, G' \cong C_p^3
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, Int(s1^(q + 1 - k))]], [3, 1, [3, Int(s1^k)]], [4, 1, [4, S1]] ]);
      od;
      for k in [1..Int((q - 1)/2)] do #Z(G) \cong C_p, G' = P
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(-1))]], [5, 1, [5, Int(s1^k)]] ]);
      od;
      for k in [1..q - 1] do #Z(G) = 1, G' \cong C_p^3
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [3, 1, [3, S1]], [4, 1, [4, S1]], [5, 1, [5, Int(s1^k)]] ]);
      od;
      if q > 2 then
        for k in [1..q - 1] do #Z(G) = 1, G' = P
          for l in [0..Int((q - 3)/2)] do
            Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^l)))]], [4, 1, [4, Int(s1^(Int(b^l) + 1))]], [5, 1, [5, Int(s1^k)]] ]);
          od;
        od;
      fi;
      if q = 2 then #Z(G) \cong C_p, G' \cong P
        Add(all, [ [2, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1)]], [5, 1, [5, (p - 1)]] ]);
      fi;
    elif (p + 1) mod q = 0 and q > 2 and p > 2 then ## q | (p + 1), Z(G) = C_p^2
      matGL2 := SOTRec.QthRootGL2P(p, q);
      Add(all, [ [q, p, p, p, p],
      [3, 2, [3, 1, 4, 1]],
      [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]],
      [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
    fi;

    #12 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ]
    if (p - 1) mod q = 0 and q > 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, S1]] ]);
      #Z(G) = 1, G' \cong C_p \ltimes C_{p^2}
    elif (p - 1) mod q = 0 and q = 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [5, 1, [4, 1, 5, (p - 1)]] ]); #Z(G) \cong C_p
      Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, (p - 1)]] ]); #Z(G) = 1, G' \cong C_p \times C_{p^2}
      Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [4, (p - 1), 5, 1]] ]); #Z(G) = 1, G' \cong P
    fi;

    #13 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ]
    if (p - 1) mod q = 0 and q > 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, Int(a), 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, S1]] ]);
      #Z(G) = 1, G' \cong C_p \ltimes C_{p^2}
    elif (p - 1) mod q = 0 and q = 2 then
      u := S2 mod p;;
      v := (S2 - u)/p;;
      x := Int((-a)^(-1));
      y := Int((-2*a)^(-1));
      Add(all, [ [2, p, p, p, p], [3, [4, Int(a)]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [5, 1, [4, 1, 5, (p - 1)]] ]); #Z(G) \cong C_p
      Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, Int(a), 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, (p - 1)]] ]); #Z(G) = 1, G' \cong C_p \times C_{p^2}
      Add(all, [ [2, p, p, p, p], [3, [4, Int(a)]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1), 4, Int(-a)]], [4, 1, [4, p - 1]], [5, 1, [4, (p - 1), 5, 1]] ]); #Z(G) = 1, G' \cong P
    fi;

    #14 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ]
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p, p, p, p], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, S1]], [4, 1, [3, Int(s1^(-1)*(s1-1)/2), 4, Int(s1^(-1))]], [5, 1, [5, Int(s1^(-2))]] ]); #Z(G) \cong C_p, G \cong C_q \ltimes (C_p \ltimes C_p^2) \times C_p
      for k in [0..q - 1] do  #Z(G) = 1 , G \cong C_q \ltimes ((C_p \ltimes C_p^2) \times C_p)
        x := s1^k;;
        v := s1^(1-k);;
        w := s1^(1-2*k);;
        y := x*(x-1)/2*w;;
        Add(all, [ [q, p, p, p, p], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, Int(x)]], [3, 1, [3, S1]], [4, 1, [3, Int(y), 4, Int(v)]], [5, 1, [5, Int(w)]] ]);
      od;
    fi;

    #15 P \cong [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] if p > 3,
    #or P \cong [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] if p = 3
    if (p - 1) mod q = 0 then
      if p > 3 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]], [4, 1, [3, Int((s1-1)/2), 4, 1]], [5, 1, [5, Int(s1^(-1))]] ]);
      elif p = 3 then
      Add(all, [ [2, p, p, p, p], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 2, 5, 1]], [2, 1, [2, 2, 4, 2]], [3, 1, [3, 2, 4, 2]], [4, 1, [4, 2]], [5, 1, [4, 1, 5, 1]] ]);
      fi;
    fi;
    #Class 3: G is solvable, no normal Sylow Subgroups
    if p = 2 and q = 3 then
      Add(all, [ [2, 2, 3, 2, 2], [3, 2, [3, 2]], [4, 2, [5, 1]], [5, 2, [4, 1]], [4, 3, [5, 1]], [5, 3, [4, 1, 5, 1]] ]); #G \cong C_2 \times Sym_4
      Add(all, [ [2, 2, 3, 2, 2], [1, [2, 1]], [3, 1, [3, 2]], [4, 1, [5, 1]], [5, 1, [4, 1]], [4, 3, [5, 1]], [5, 3, [4, 1, 5, 1]] ]); #C_4 \ltimes Alt_4
      Add(all, [ [2, 3, 2, 2, 2], [3, [5, 1]], [4, [5, 1]], [3, 2, [4, 1, 5, 1]], [4, 2, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]], [2, 1, [2, 2]], [3, 1, [4, 1]], [4, 1, [3, 1]] ]); #G \cong C_2 \ltimes (C_3 \ltimes Q_8)
      Add(all, [ [2, 3, 2, 2, 2], [1, [5, 1]], [3, [5, 1]], [4, [5, 1]], [3, 2, [4, 1, 5, 1]], [4, 2, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]], [2, 1, [2, 2]], [3, 1, [4, 1]], [4, 1, [3, 1]] ]); #G \cong C_2 . (C_3 \ltimes Q_8)
    elif p = 3 and q = 13 then #(q = 13, p = 3)
      matGL3 := SOTRec.QthRootGL3P(p, q);
      m := [ [ 0, 2, 1 ], [ 1, 2, 2 ], [ 1, 1, 1 ] ];
      Add(all, [ [p, q, p, p, p], [2, 1, [2, R1]],
      [3, 1, [3, m[1][1], 4, m[2][1], 5, m[3][1]]],
      [4, 1, [3, m[1][2], 4, m[2][2], 5, m[3][2]]],
      [5, 1, [3, m[1][3], 4, m[2][3], 5, m[3][3]]],
      [3, 2, [3, Int(matGL3[1][1]), 4, Int(matGL3[2][1]), 5, Int(matGL3[3][1])]],
      [4, 2, [3, Int(matGL3[1][2]), 4, Int(matGL3[2][2]), 5, Int(matGL3[3][2])]],
      [5, 2, [3, Int(matGL3[1][3]), 4, Int(matGL3[2][3]), 5, Int(matGL3[3][3])]] ]);
    fi;
    if Length(arg) = 0 then
      return List(all, x -> SOTRec.groupFromData(x));
    else
      return all;
    fi;
end;
###################################################################
SOTRec.GroupP4Q := function(p, q, id)
  local all, list, a, b, c, d, e, f, g, h, r1, r2, r3, r4, s1, s2, s3, s4, u, v, w, x, y,
        R1, R2, R3, R4, S1, S2, S3, S4, mat, matGL2, matGL3, matGL4, func, TupleiById, i, j, k, l, m,
        C0, C, data;
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));

    a := Z(p);
    b := Z(q);
    if (q - 1) mod p = 0 then
      r1 := b^((q-1)/p);
      R1 := Int(r1);
    fi;
    if (q - 1) mod (p^2) = 0 then
      r2 := b^((q-1)/(p^2));
      R2 := Int(r2);
    fi;
    if (q - 1) mod (p^3) = 0 then
      r3 := b^((q-1)/(p^3));
      R3 := Int(r3);
    fi;
    if (q - 1) mod (p^4) = 0 then
      r4 := b^((q-1)/(p^4));
      R4 := Int(r4);
    fi;
    if (p - 1) mod q = 0 then
      if not Int(a)^(p - 1) mod p^2 = 1 then
        c := ZmodnZObj(Int(a), p^2);
        d := ZmodnZObj(Int(a), p^3);
        e := ZmodnZObj(Int(a), p^4);
      else
        c := ZmodnZObj(Int(a) + p, p^2);
        d := ZmodnZObj(Int(a) + p, p^3);
        e := ZmodnZObj(Int(a) + p, p^4);
      fi;
      s1 := a^((p - 1)/q);;
      s2 := c^((p^2 - p)/q);;
      s3 := d^((p^3 - p^2)/q);;
      s4 := e^((p^4 - p^3)/q);;
      S1 := Int(s1);;
      S2 := Int(s2);;
      S3 := Int(s3);;
      S4 := Int(s4);;
    fi;
    ##construct all nilpotent groups:
    all := [];
    C0 := 15 - SOTRec.delta(2, p);
    C := [];
    C[1] := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3) + SOTRec.w((q - 1), p^4);
    C[2] := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3);
    C[3] := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    C[4] := 2*SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    C[5] := SOTRec.w((q - 1), p);
    C[6] := 3*SOTRec.w((q - 1), p);
    C[7] := (1 - SOTRec.delta(2, p))*(p*SOTRec.w((q - 1), p) + p*SOTRec.w((q - 1), p^2)) + 3*SOTRec.delta(2, p);
    C[8] := (1 - SOTRec.delta(2, p))*(p + 1)*SOTRec.w((q - 1), p) + SOTRec.delta(2, p)*(2 + SOTRec.w((q - 1), 4));
    C[9] := 2*SOTRec.w((q - 1), p) + (1 - SOTRec.delta(2, p))*SOTRec.w((q - 1), p^2);
    C[10] := p*SOTRec.w((q - 1), p) + (p - 1)*SOTRec.w((q - 1), p^2);
    C[11] := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), 4)*SOTRec.delta(2, p);
    C[12] := p*SOTRec.w((q - 1), p) + SOTRec.delta(2, p);
    C[13] := p*SOTRec.w((q - 1), p) - SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    C[14] := 2*SOTRec.w((q - 1), p) + SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    C[15] := (1 - SOTRec.delta(2, p))*2*SOTRec.w((q - 1), p);
    C[16] := SOTRec.w((p - 1), q);
    C[17] := (q + 1)*SOTRec.w((p - 1), q);
    C[18] := 1/2*(q + 3 - SOTRec.delta(2, q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    C[19] := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q);
    C[20] := 1/24*(q^3 + 7*q^2 + 21*q + 39 + 16*SOTRec.w((q - 1), 3) + 12*SOTRec.w((q - 1), 4))*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(2, q)) + 4*SOTRec.delta(2, q)
        + 1/4*(q + 5 + 2*SOTRec.w((q - 1), 4))*SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q))
        + SOTRec.w((p^2 + p +1), q)*(1 - SOTRec.delta(3, q))
        + SOTRec.w((p^2 + 1), q)*(1 - SOTRec.delta(2, q));
    C[21] := 1/2*(q + 3 - SOTRec.delta(2,q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    C[22] := SOTRec.w((p - 1), q);
    C[23] := (q + 1)*SOTRec.w((p - 1), q);
    C[24] := (q + 1)*SOTRec.w((p - 1), q) + SOTRec.delta([p,q], [2,3]);
    C[25] := SOTRec.w((p - 1), q);
    C[26] := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q) - SOTRec.delta([p,q], [2,3]);
    C[27] := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    C[28] := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    C[29] := (q + 1)*SOTRec.w((p - 1), q);
    C[30] := SOTRec.w((p - 1), q);

    if id < C0 + 1 then
      data := SOTRec.lowpowerPGroups(p, 4, 0)[id];
      Add(data[1], q);
      return SOTRec.groupFromData(data);
    ##Class 1: Group G is solvable, nonnilpotent. Sylow p-subgroup is normal in G. Thus G \cong C_q \ltimes P is a nonabelian split extension.
    ##Isomorphism types of such groups are in one-to-one correspondence with the conjugacy classes of cyclic subgroups of order q in \Aut P.

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    #1 P \cong C_{p^4}
    elif id > C0 and id < C0 + C[1] + 1 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]);
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]);
      fi;
      if (q - 1) mod p^3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]);
      fi;
      if (q - 1) mod p^4 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, R4]], [5, 2, [5, R3]], [5, 3, [5, R2]], [5, 4, [5, R1]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0]);

    #2 P \cong C_{p^3} \times C_p
    elif id > C0 + C[1] and id < C0 + Sum([1..2],x->C[x]) + 1 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 4, [5, R1]] ]); #Z(G) \cong C_{p^3}
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2}
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
      fi;
      if (q - 1) mod p^3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [5, 1, [5, R3]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #Z(G) \cong C_p
      fi;
      return SOTRec.groupFromData(all[id - C0 - C[1]]);

    #3 P \cong C_{p^2} \times C_{p^2}
    elif id > C0 + Sum([1..2],x->C[x]) and id < C0 + Sum([1..3],x->C[x]) + 1 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, [4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_{p^2}
      fi;
      return SOTRec.groupFromData(all[id - C0 - C[1] - C[2]]);

    #4 P \cong C_{p^2} \times C_p^2
    elif id > C0 + Sum([1..3],x->C[x]) and id < C0 + Sum([1..4],x->C[x]) + 1 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 3, [5, R1]] ]); #Z(G) \cong C_{p^2} \times C_p
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
      fi;
      if (q - 1) mod p^2 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #Z(G) \cong C_p^2
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..3],x->C[x])]);

    #5 P \cong C_p^4
    elif id > C0 + Sum([1..4],x->C[x]) and id < C0 + Sum([1..5],x->C[x]) + 1 then
      if (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [5, 1, [5, R1]] ]); #Z(G) \cong C_p^3
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..4],x->C[x])]);

    #6 P \cong [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or P \cong [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..5],x->C[x]) and id < C0 + Sum([1..6],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong p_- \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \ltimes F(G), Z(G) \cong C_4
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong D_4 \times C_q, G \cong C_2 \ltimes (C_4 \ltimes C_q \times C_2), Z(G) \cong C_2
        Add(all, [ [2, 2, 2, 2, q], [2, [4, 1]], [3, [4, 1]], [3, 1, [3, 1, 4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]);#F(G) \cong Q_8 \times C_q, G \cong C_2 \ltimes (Q_8 \ltimes C_q), Z(G) \cong C_2
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..5],x->C[x])]);

    #7 P \cong [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
  elif id > C0 + Sum([1..6],x->C[x]) and id < C0 + Sum([1..7],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          for k in [1..p - 1] do
            Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, Int(r1^k)]] ]); #F(G) \cong C_{p^3} \times C_q
          od;
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        fi;
        if (q - 1) mod p^2 = 0 then
          for k in [1..p - 1] do #F(G) \cong C_{p^2} \times C_q
            Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [4, 1]], [3, [4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r2^k)]], [5, 2, [5, Int(r1^k)]] ]);
          od;
          Add(all, [ [p, p, p, p, q], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R2]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]);#F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \times D_{4q}
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, q - 1]] ]);#F(G) \cong D_4 \times C_q, G \cong D_q \times D_4
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, q - 1]] ]);#F(G) \cong C_q \times C_2^3, G \cong (D_4 \ltimes C_q) \times C_2
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..6],x->C[x])]);


    #8 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ]
    elif id > C0 + Sum([1..7],x->C[x]) and id < C0 + Sum([1..8],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          for k in [1..p - 1] do #F(G) \cong (C_p \times C_{p^2}) \times C_q
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]);
          od;
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_- \times C_q
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \ltimes F(G), Z(G) \cong C_2^2
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_2^3 \times C_q, G \cong C_2 \ltimes (C_4 \ltimes C_q \times C_2)
        if (q - 1) mod (p^2) = 0 then
          Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_2^2 \times C_q, G \cong C_2 \ltimes ((C_4 \ltimes C_q) \times C_2)
        fi;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..7],x->C[x])]);

    #9 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    elif id > C0 + Sum([1..8],x->C[x]) and id < C0 + Sum([1..9],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        fi;
        if (q - 1) mod p^2 = 0 then
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, R1]] ]); #F(G) \cong C_p^2 \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong (C_4 \times C_2) \times C_q, G \cong C_2 \times (Q_8 \ltimes C_q)
        Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 4, [5, q - 1]] ]); #F(G) \cong Q_8 \times C_q, G \cong D_q \times Q_8
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..8],x->C[x])]);

    #10 P \cong [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ]
    elif id > C0 + Sum([1..9],x->C[x]) and id < C0 + Sum([1..10],x->C[x]) + 1 then
      if p > 2 then
          if (q - 1) mod p = 0 then #F(G) \cong (C_p \times C_{p^2}) \times C_q
            Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, R1]] ]);
            for k in [1..p - 1] do #F(G) \cong (C_p \times C_{p^2}) \times C_q
              Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r1^k)]] ]);
            od;
          fi;
          if (q - 1) mod p^2 = 0 then #F(G) \cong C_{p^2} \times C_q
            for k in [1..p - 1] do
              Add(all, [ [p, p, p, p, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, Int(r2^k)]], [5, 4, [5, Int(r1^k)]] ]);
            od;
          fi;
        elif p = 2 then
          Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times (C_4 \times C_2)
          Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times (C_4 \times C_2)
          if (q - 1) mod (p^2) = 0 then
            Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [5, 1, [5, R2]], [5, 4, [5, q - 1]] ]); #F(G) \cong C_q \times C_4
          fi;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..9],x->C[x])]);

    #11 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]] ]
  elif id > C0 + Sum([1..10],x->C[x]) and id < C0 + Sum([1..11],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
          Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times C_4 \times C_2
        if (q - 1) mod p^2 = 0 then
          Add(all, [ [2, 2, 2, 2, q], [1, [3, 1]], [2, [4, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 1, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_q \times C_4
          Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]], [5, 2, [5, R2]], [5, 3, [5, q - 1]] ]); #F(G) \cong C_q \times C_2^2
        fi;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..10],x->C[x])]);

    #12 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1,[3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..11],x->C[x])
      and id < C0 + Sum([1..12],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          for k in [1..(p - 1)/2] do
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
          od;
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
          if p > 3 then
            for k in [1..(p - 1)/2] do #F(G) \cong p_- \times C_q
              Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]);
            od;
          else #p = 3
            Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 2]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, p - 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong 3_- \times C_q
          fi;
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times D_4
        Add(all, [ [2, 2, 2, 2, q], [2, [4, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times Q_8
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..11],x->C[x])]);

    #13 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..12],x->C[x])
      and id < C0 + Sum([1..13],x->C[x]) + 1 then
      if p > 3 and (q - 1) mod p = 0 then
        for k in [1..(p - 1)/2] do
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 1, [5, Int(r1^k)]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        od;
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        for k in [1..(p - 1)/2] do #F(G) \cong p_- \times C_q
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [4, 1, [3, Int(a), 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, Int(r1^k)]] ]);
        od;
      elif p = 3 and (q - 1) mod 3 = 0 then
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_+ \times C_q
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
        Add(all, [ [2, 2, 2, 2, q], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times D_4
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..12],x->C[x])]);

    #14 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..13],x->C[x])
      and id < C0 + Sum([1..14],x->C[x]) + 1 then
      if p > 2 then
        if (q - 1) mod p = 0 then
          Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
          Add(all, [ [p, p, p, p, q], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_+ \times C_q
        fi;
        if p = 3 and (q - 1) mod p = 0 then
          Add(all, [ [p, p, p, p, q], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]], [4, 2, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong 3_- \times C_q
        fi;
      elif p = 2 then
        Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 1, [5, q - 1]] ]); #F(G) \cong C_q \times C_8
        Add(all, [ [2, 2, 2, 2, q], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]], [5, 2, [5, q - 1]] ]); #F(G) \cong C_q \times Q_8
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..13],x->C[x])]);

    #15 P \cong [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] if p > 3,
    #or P \cong [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] if p = 3
    elif id > C0 + Sum([1..14],x->C[x])
      and id < C0 + Sum([1..15],x->C[x]) + 1 then
      if p > 3 and (q - 1) mod p = 0 then
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong C_p^3 \times C_q
        Add(all, [ [p, p, p, p, q], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]], [5, 4, [5, R1]] ]); #F(G) \cong p_- \times C_q
      fi;
      if p = 3 and (q - 1) mod 3 = 0 then
        Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 1, [5, R1]] ]); #F(G) \cong (C_p \times C_{p^2}) \times C_q
        Add(all, [ [p, p, p, p, q], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]], [5, 2, [5, R1]] ]); #F(G) \cong p_- \times C_q
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..14],x->C[x])]);

    ##Class 2: Group G is solvable, nonnilpotent. Sylow q-subgroup is normal in G. Thus G \cong P \ltimes C_q is a nonabelian split extension.
    #1 P \cong C_{p^4}
    elif id > C0 + C[1] + C[2] + C[3] + C[4] + C[5] + C[6] + C[7] + C[8] + C[9] + C[10] + C[11] + C[12] + C[13] + C[14] + C[15]
      and id < C0 + C[1] + C[2] + C[3] + C[4] + C[5] + C[6] + C[7] + C[8] + C[9] + C[10] + C[11] + C[12] + C[13] + C[14] + C[15] + C[16] + 1 then
      if (p - 1) mod q = 0 then
        u := S4 mod p;
        v := (S4 - u)/p mod p;
        x := ((S4 - u)/p - v)/p mod p;
        y := (((S4 - u)/p - v)/p - x)/p;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v, 4, x, 5, y]], [3, 1, [3, u, 4, v, 5, x]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #unique
      fi;
      return SOTRec.groupFromData(all[id - C0 - C[1] - C[2] - C[3] - C[4] - C[5] - C[6] - C[7] - C[8] - C[9] - C[10] - C[11] - C[12] - C[13] - C[14] - C[15]]);

    #2 P \cong C_{p^3} \times C_p
    elif id > C0 + Sum([1..16],x->C[x])
      and id < C0 + Sum([1..17],x->C[x]) + 1 then
        if (p - 1) mod q = 0 then
          u := S3 mod p;
          v := (S3 - u)/p mod p;
          x := ((S3 - u)/p - v)/p;
          Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p
          Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_{p^3}
          for k in [1..(q - 1)] do
            Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, Int(s1^k)]] ]); #Z(G) = 1
          od;
        fi;
        return SOTRec.groupFromData(all[id - C0 - Sum([1..16],x->C[x])]);

    #3 P \cong C_{p^2} \times C_{p^2}
    elif id > C0 + Sum([1..17],x->C[x])
      and id < C0 + Sum([1..18],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        u := S2 mod p;
        v := (S2 - u)/p;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]] ]); #Z(G) \cong C_{p^2}
        for k in [0..Int((q - 1)/2)] do
          x := Int(s2^(Int(b^k))) mod p;
          y := (Int(s2^(Int(b^k))) - x)/p;
          Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, [5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]], [4, 1, [4, x, 5, y]], [5, 1, [5, x]] ]); #Z(G) = 1
        od;
      elif (p + 1) mod q = 0 and q > 2 then
        mat := SOTRec.QthRootM2P2(p, q);
        Add(all, [ [q, p, p, p, p], [2, [4, 1]], [3, [5, 1]],
        [2, 1, [2, mat[1][1], 3, mat[2][1], 4, mat[3][1], 5, mat[4][1]]],
        [3, 1, [2, mat[1][2], 3, mat[2][2], 4, mat[3][2], 5, mat[4][2]]],
        [4, 1, [2, mat[1][3], 3, mat[2][3], 4, mat[3][3], 5, mat[4][3]]],
        [5, 1, [2, mat[1][4], 3, mat[2][4], 4, mat[3][4], 5, mat[4][4]]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..17],x->C[x])]);

    #4 P \cong C_{p^2} \times C_p^2
    elif id > C0 + Sum([1..18],x->C[x])
      and id < C0 + Sum([1..19],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]] ]); #Z(G) \cong C_p \times C_{p^2}
        for k in [0..Int((q - 1)/2)] do #Z(G) \cong C_{p^2}
          Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^k)))]] ]);
        od;
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]); #Z(G) \cong C_p^2
        for k in [1..(q - 1)] do #Z(G) \cong C_p
          Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]);
        od;
        #below trivial centre
        for k in [1..(q - 1)] do
          for l in [k + 1..(q - 1)] do;
            Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [3, 1, [3, Int(s1^l)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]);
          od;
        od;
        for k in [1..(q - 1)] do
          Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(s1^k)]], [3, 1, [3, Int(s1^k)]], [4, 1, [4, u, 5, v]], [5, 1, [5, u]] ]);
        od;
      elif (p + 1) mod q = 0 and q > 2 then
        matGL2 := SOTRec.QthRootGL2P(p, q);
        Add(all, [ [q, p, p, p, p], [4, [5, 1]], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..18],x->C[x])]);

    #5 P \cong C_p^4
    elif id > C0 + Sum([1..19],x->C[x])
      and id < C0 + Sum([1..20],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        if id < C0 + Sum([1..19],x->C[x])
          + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + 1/2*(q^2 - 2*q + 3)*SOTRec.w((p - 1), q) + 1 then
          Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]] ]); #Z(G) \cong C_p^3, G \cong (C_q \ltimes C_p) \times C_p^3
          for k in [0..Int((q - 1)/2)] do
            Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^Int(b^k))]] ]); #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
          od;
          #below Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
          if q = 2 then
            Add(all, [ [q, p, p ,p, p], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1)]], [4, 1, [4, (p - 1)]] ]);
          elif q = 3 then
            for k in [0, 1] do
              Add(all, [ [q, p, p ,p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]] ]);
            od;
          else #q > 3
            for k in [1..(q - 1)] do
              Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^k)]] ]);
            od;
            func := function(q)
              local qq, res, a,b,c,d,t,bb;
                res :=[];
                qq  := q-1;
                bb  := (q-1) mod 3;
                bb  := (q-1-bb) / 3;
                for a in [1..bb] do
                  for b in [2*a..(q-2-a)] do
                    t := [[-a,b-a],[-b,a-b]] mod qq;
                    if ForAll(t,x-> [a,b] <= SortedList(x))  then
                     Add(res,[a,b]);
                    fi;
                  od;
                od;
                if (q - 1) mod 3 = 0 then
                  Add(res, [bb, 2*bb]);
                fi;
              return res;
            end; #explength := 1/6*(q^2 - 5*q + 6 + 4*SOTRec.w((q - 1), 3));
            for k in func(q) do
              Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]] ]);
            od;
          fi;
          #below: Z(G) = 1, G \cong C_q \ltimes C_p^4
          for k in [0..(q - 2)] do
            Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, S1]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
          od;
          for k in [1..Int((q - 1)/2)] do
            Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^k)))]] ]);
          od;
          for k in [1..(q - 2)] do
            for l in [k + 1..(q - 2)] do
              Add(all, [ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, S1]], [4, 1, [4, Int(s1^(Int(b^k)))]], [5, 1, [5, Int(s1^(Int(b^l)))]] ]);
            od;
          od;
          return SOTRec.groupFromData(all[id - C0 - Sum([1..19],x->C[x])]);

        elif id > C0 + Sum([1..19],x->C[x])
          + (1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + 1/2*(q^2 - 2*q + 3))*SOTRec.w((p - 1), q) then
          TupleiById := function(q,id)
          local qq, res, a,b,c,d,t,cnt;
              qq := q - 1;
               cnt := 0;
               for a in [1..Int((q-1)/4)] do
                  for b in [2*a..(q-1)/2] do
                     if cnt + (q-2-a-b-a+1) < id then
               cnt := cnt + q-2-a-b-a+1;
            else
               return [a,b, (b+a) + (id-cnt-1)];
            fi;
                 od;
                 for b in [(q+1)/2..p-1-2*a] do
                     if cnt + Maximum((q-2-a-b-a),0) < id then
                 cnt := cnt + Maximum(q-2-a-b-a,0);
              else
                 return [a,b, (b+a+1) + (id-cnt-1)];
              fi;
                od;
              od;
               if qq mod 4 = 0 and id = 1/24*(q^3- 9*q^2+29*q-33 + 12*SOTRec.w((q - 1), 4)) then
                 return  [(q-1)/4, (q-1)/2, 3*(q-1)/4];
               fi;
            end;
            k := TupleiById(q, id - C0 - Sum([1..19],x->C[x])  - (1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + 1/2*(q^2 - 2*q + 3))*SOTRec.w((p - 1), q));
            return SOTRec.groupFromData([ [q, p, p, p, p], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^(k[1]))))]], [4, 1, [4, Int(s1^(Int(b^(k[2]))))]], [5, 1, [5, Int(s1^(Int(b^(k[3]))))]] ]);
        fi;

      elif (p + 1) mod q = 0 and q > 2 then #Z(G) \cong C_p^2, G \cong (C_q \ltimes C_p^2) \times C_p^2
        matGL2 := SOTRec.QthRootGL2P(p, q);
        Add(all, [ [q, p, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
        for k in [0..Int((q - 1)/4)] do #Z(G) \cong 1, G \cong C_q \ltimes C_p^4
          m := matGL2^(Int(b^k));;
          Add(all, [ [q, p, p, p, p], [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]], [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]],
           [4, 1, [4, Int(m[1][1]), 5, Int(m[2][1])]], [5, 1, [4, Int(m[1][2]), 5, Int(m[2][2])]] ]);
         od;
      elif (p^2 + p + 1) mod q = 0 and q > 3 then #Z(G) \cong C_p, G \cong (C_q \ltimes C_p^3) \times C_p
        matGL3 := SOTRec.QthRootGL3P(p, q);
        Add(all, [ [q, p, p, p, p],
        [2, 1, [2, Int(matGL3[1][1]), 3, Int(matGL3[2][1]), 4, Int(matGL3[3][1])]],
        [3, 1, [2, Int(matGL3[1][2]), 3, Int(matGL3[2][2]), 4, Int(matGL3[3][2])]],
        [4, 1, [2, Int(matGL3[1][3]), 3, Int(matGL3[2][3]), 4, Int(matGL3[3][3])]] ]);
      elif (p^2 + 1) mod q = 0 and q > 3 then #Z(G) = 1, G \cong C__q \ltimes C_p^4
        matGL4 := SOTRec.QthRootGL4P(p,q);
        Add(all, [ [q, p, p, p, p],
        [2, 1, [2, Int(matGL4[1][1]), 3, Int(matGL4[2][1]), 4, Int(matGL4[3][1]), 5, Int(matGL4[4][1])]],
        [3, 1, [2, Int(matGL4[1][2]), 3, Int(matGL4[2][2]), 4, Int(matGL4[3][2]), 5, Int(matGL4[4][2])]],
        [4, 1, [2, Int(matGL4[1][3]), 3, Int(matGL4[2][3]), 4, Int(matGL4[3][3]), 5, Int(matGL4[4][3])]],
        [5, 1, [2, Int(matGL4[1][4]), 3, Int(matGL4[2][4]), 4, Int(matGL4[3][4]), 5, Int(matGL4[4][4])]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - C[1] - C[2] - C[3] - C[4] - C[5] - C[6] - C[7] - C[8] - C[9] - C[10] - C[11] - C[12] - C[13] - C[14] - C[15]
      - C[16] - C[17] - C[18] - C[19]]);

    #6 P \cong [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [3, [4, 1]], [2, 1, [2, 1, 4, 1]] ]
    elif id > C0 + Sum([1..20],x->C[x])
      and id < C0 + Sum([1..21],x->C[x])  + 1 then
      if (p - 1) mod q = 0 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [5, 1, [5, S1]], [2, 1, [2, Int(s1^-1)]] ]); #Z(G) \cong C_{p^2}, G \cong C_q \ltimes (C_p \ltimes (C_p \times C_{p^2}))
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [2, 1, [2, S1]] ]); #Z(G) = 1, , G \cong C_q \ltimes (C_p \ltimes (C_p \ltimes C_{p^2})), G' \cong C_p \times C_{p^2}
        for k in [2..Int((q + 1)/2)] do
          Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, Int(s1^k)]], [2, 1, [2, Int(s1^(q + 1 - k))]] ]); #Z(G) = 1, G \cong C_q \ltimes (C_p \ltimes p_-)
        od;
      elif (p + 1) mod q = 0 and q > 2 and p > 2 then
        matGL2 := SOTRec.QthRootGL2P(p, q);
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [5, 2, [4, 1, 5, 1]],
        [2, 1, [2, Int(matGL2[1][1]), 5, Int(matGL2[2][1])]],
        [5, 1, [2, Int(matGL2[1][2]), 5, Int(matGL2[2][2])]] ]);
      elif p = 2 and q = 3 then ##PROVE?DOUBLE CHECK
        Add(all, [ [3, 2, 2, 2, 2], [2, [5, 1]], [3, [5, 1]], [4, [5, 1]], [3, 1, [4, 1]], [4, 1, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..20],x->C[x]) ]);

    #7 P \cong [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ]

    elif id > C0 + Sum([1..21],x->C[x])
      and id < C0 + Sum([1..22],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        u := S3 mod p;
        v := (S3 - u)/p mod p;
        x := ((S3 - u)/p - v)/p;
        Add(all, [ [q, p, p, p, p], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, u, 3, v, 4, x]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 2, [4, 1, 5, 1]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..21],x->C[x])]);

    #8 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    elif id > C0 + Sum([1..22],x->C[x])
        and id < C0 + Sum([1..23],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, (C_q \ltimes C_p) \times (C_p \ltimes C_{p^2}), G' \cong C_p^2
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, G \cong (C_q \ltimes (C_p \ltimes C_{p^2})) \times C_p, G' \cong C_{p^2}
        for k in [1..q - 1] do #Z(G) = 1
          Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [5, 1, [5, Int(s1^k)]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]);
        od;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..22],x->C[x])]);

    #9 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ], p > 2
    #or [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    elif id > C0 + Sum([1..23],x->C[x])
        and id < C0 + Sum([1..24],x->C[x]) + 1 then
      if (p - 1) mod q = 0 and p > 2 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, S1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, G \cong (C_q \ltimes (C_p \ltimes C_{p^2})) \times C_p, G' \cong C_p^2
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, Int(s1^(-1))]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, C_q \ltimes (C_p \ltimes (C_p \times C_{p^2})), G' \cong P
        for k in [1..q - 2] do #Z(G) = 1, G \cong , G' \cong P
          x := Int(s2^k) mod p;;
          y := (Int(s2^k) - x)/p;;
          Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [2, 1, [2, S1]], [5, 1, [5, Int(s1^(k+1))]], [3, 1, [3, x, 4, y]], [4, 1, [4, x]] ]);
        od;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 1, [5, S1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) = 1, G \cong C_q \ltimes (C_p \ltimes (C_p \times C_{p^2}), G' \cong C_p \times C_{p^2}
      elif p = 2 and q = 3 then
        Add(all, [ [3, 2, 2, 2, 2], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ]); #Z(G) \cong C_2^2
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..23],x->C[x])]);

    #10 P \cong [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ]
    elif id > C0 + Sum([1..24],x->C[x])
        and id < C0 + Sum([1..25],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [2, [5, 1]], [3, [4, 1]], [3, 2, [3, 1, 4, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]] ]); #Z(G) \cong C_p, G \cong C_q \ltimes (C_{p^2} \ltimes C_{p^2})
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..24],x->C[x])]);

    #11 P \cong [ [p, p, p, p], [2, 1, [2, 1, 3, 1]] ] HARD!
    elif id > C0 + Sum([1..25],x->C[x])
        and id < C0 + Sum([1..26],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, Int(s1^(-1))]], [3, 1, [3, S1]] ]); #Z(G) \cong C_p^2, G' \cong C_p^3
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [5, 1, [5, S1]] ]); #Z(G) \cong C_p, G' \cong C_p^2
        Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [4, 1, [4, S1]] ]); #Z(G) \cong C_p, G' \cong C_p^2
        for k in [2..Int((q + 1)/2)] do #Z(G) \cong C_p, G' \cong C_p^3
          Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, Int(s1^(q + 1 - k))]], [3, 1, [3, Int(s1^k)]], [4, 1, [4, S1]] ]);
        od;
        for k in [1..Int((q - 1)/2)] do #Z(G) \cong C_p, G' = P
          Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(-1))]], [5, 1, [5, Int(s1^k)]] ]);
        od;
        for k in [1..q - 1] do #Z(G) = 1, G' \cong C_p^3
          Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [3, 1, [3, S1]], [4, 1, [4, S1]], [5, 1, [5, Int(s1^k)]] ]);
        od;
        if q > 2 then
          for k in [1..q - 1] do #Z(G) = 1, G' = P
            for l in [0..Int((q - 3)/2)] do
              Add(all, [ [q, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, S1]], [3, 1, [3, Int(s1^(Int(b^l)))]], [4, 1, [4, Int(s1^(Int(b^l) + 1))]], [5, 1, [5, Int(s1^k)]] ]);
            od;
          od;
        fi;

        if q = 2 then #Z(G) \cong C_p, G' \cong P
          Add(all, [ [2, p, p, p, p], [3, 2, [3, 1, 4, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1)]], [5, 1, [5, (p - 1)]] ]);
        fi;
      elif (p + 1) mod q = 0 and q > 2 and p > 2 then ## q | (p + 1), Z(G) = C_p
        matGL2 := SOTRec.QthRootGL2P(p, q);
        Add(all, [ [q, p, p, p, p],
        [3, 2, [3, 1, 4, 1]],
        [2, 1, [2, Int(matGL2[1][1]), 3, Int(matGL2[2][1])]],
        [3, 1, [2, Int(matGL2[1][2]), 3, Int(matGL2[2][2])]] ]);
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..25],x->C[x])]);

    #12 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..26],x->C[x])
        and id < C0 + Sum([1..27],x->C[x]) + 1 then
      if (p - 1) mod q = 0 and q > 2 then #Z(G) = 1, G' \cong C_p \ltimes C_{p^2}
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, S1]] ]);

      elif (p - 1) mod q = 0 and q = 2 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [5, 1, [4, 1, 5, (p - 1)]] ]); #Z(G) \cong C_p
        Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, (p - 1)]] ]); #Z(G) = 1, G' \cong C_p \times C_{p^2}
        Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [4, (p - 1), 5, 1]] ]); #Z(G) = 1, G' \cong P
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..26],x->C[x])]);

    #13 P \cong [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ]
    elif id > C0 + Sum([1..27],x->C[x])
        and id < C0 + Sum([1..28],x->C[x]) + 1 then
      if (p - 1) mod q = 0 and q > 2 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        Add(all, [ [q, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, Int(a), 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, S1]] ]);
        #Z(G) = 1, G' \cong C_p \ltimes C_{p^2}
      elif (p - 1) mod q = 0 and q = 2 then
        u := S2 mod p;;
        v := (S2 - u)/p;;
        x := Int((-a)^(-1));
        y := Int((-2*a)^(-1));
        Add(all, [ [2, p, p, p, p], [3, [4, Int(a)]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [5, 1, [4, 1, 5, (p - 1)]] ]); #Z(G) \cong C_p
        Add(all, [ [2, p, p, p, p], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, Int(a), 5, 1]], [3, 1, [3, u, 4, v]], [4, 1, [4, u]], [5, 1, [5, (p - 1)]] ]); #Z(G) = 1, G' \cong C_p \times C_{p^2}
        Add(all, [ [2, p, p, p, p], [3, [4, Int(a)]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, (p - 1)]], [3, 1, [3, (p - 1), 4, Int(-a)]], [4, 1, [4, p - 1]], [5, 1, [4, (p - 1), 5, 1]] ]); #Z(G) = 1, G' \cong P
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..27],x->C[x])]);

    #14 P \cong [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ]
    elif id > C0 + Sum([1..28],x->C[x])
        and id < C0 + Sum([1..29],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        Add(all, [ [q, p, p, p, p], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, S1]], [4, 1, [3, Int(s1^(-1)*(s1-1)/2), 4, Int(s1^(-1))]], [5, 1, [5, Int(s1^(-2))]] ]); #Z(G) \cong C_p, G \cong C_q \ltimes (C_p \ltimes C_p^2) \times C_p
        for k in [0..q - 1] do  #Z(G) = 1
          x := s1^k;;
          v := s1^(1-k);;
          w := s1^(1-2*k);;
          y := x*(x-1)/2*w;;
          Add(all, [ [q, p, p, p, p], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, Int(x)]], [3, 1, [3, S1]], [4, 1, [3, Int(y), 4, Int(v)]], [5, 1, [5, Int(w)]] ]);
        od;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..28],x->C[x])]);

    #15 P \cong [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] if p > 3,
    #or P \cong [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] if p = 3
    elif id > C0 + Sum([1..29],x->C[x])
        and id < C0 + Sum([1..30],x->C[x]) + 1 then
      if (p - 1) mod q = 0 then
        if p > 3 then
          u := S2 mod p;;
          v := (S2 - u)/p;;
          Add(all, [ [q, p, p, p, p], [2, [3, 1]], [4, 2, [3, 1, 4, 1]], [5, 2, [4, 1, 5, 1]], [2, 1, [2, u, 3, v]], [3, 1, [3, u]], [4, 1, [3, Int((s1-1)/2), 4, 1]], [5, 1, [5, Int(s1^(-1))]] ]);
        elif p = 3 then
        Add(all, [ [2, p, p, p, p], [2, [4, 1]], [3, [4, 1]], [3, 2, [3, 1, 5, 1]], [5, 2, [4, 2, 5, 1]], [2, 1, [2, 2, 4, 2]], [3, 1, [3, 2, 4, 2]], [4, 1, [4, 2]], [5, 1, [4, 1, 5, 1]] ]);
        fi;
      fi;
      return SOTRec.groupFromData(all[id - C0 - Sum([1..29],x->C[x])]);

    #Class 3: G is solvable, no normal Sylow Subgroups
    elif p = 2 and q = 3 and id > 48 and id < 53 then
      Add(all, [ [2, 2, 3, 2, 2], [3, 2, [3, 2]], [4, 2, [5, 1]], [5, 2, [4, 1]], [4, 3, [5, 1]], [5, 3, [4, 1, 5, 1]] ]); #G \cong C_2 \times Sym_4
      Add(all, [ [2, 2, 3, 2, 2], [1, [2, 1]], [3, 1, [3, 2]], [4, 1, [5, 1]], [5, 1, [4, 1]], [4, 3, [5, 1]], [5, 3, [4, 1, 5, 1]] ]); #C_4 \ltimes Alt_4
      Add(all, [ [2, 3, 2, 2, 2], [3, [5, 1]], [4, [5, 1]], [3, 2, [4, 1, 5, 1]], [4, 2, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]], [2, 1, [2, 2]], [3, 1, [4, 1]], [4, 1, [3, 1]] ]); #G \cong C_2 \ltimes (C_3 \ltimes Q_8)
      Add(all, [ [2, 3, 2, 2, 2], [1, [5, 1]], [3, [5, 1]], [4, [5, 1]], [3, 2, [4, 1, 5, 1]], [4, 2, [3, 1, 4, 1]], [4, 3, [4, 1, 5, 1]], [2, 1, [2, 2]], [3, 1, [4, 1]], [4, 1, [3, 1]] ]); #G \cong C_2 . (C_3 \ltimes Q_8)
      return SOTRec.groupFromData(all[id - C0 - C[1] - C[2] - C[3] - C[4] - C[5] - C[6] - C[7] - C[8] - C[9] - C[10] - C[11] - C[12] - C[13] - C[14] - C[15]
      - C[16] - C[17] - C[18] - C[19] - C[20] - C[21] - C[22] - C[23] - C[24] - C[25] - C[26] - C[27] - C[28] - C[29] - C[30]]);
    elif p = 3 and q = 13 and id = 51 then
      matGL3 := SOTRec.QthRootGL3P(p, q);
      m := [ [ 0, 2, 1 ], [ 1, 2, 2 ], [ 1, 1, 1 ] ];
      return SOTRec.groupFromData([ [p, q, p, p, p], [2, 1, [2, R1]],
      [3, 1, [3, m[1][1], 4, m[2][1], 5, m[3][1]]],
      [4, 1, [3, m[1][2], 4, m[2][2], 5, m[3][2]]],
      [5, 1, [3, m[1][3], 4, m[2][3], 5, m[3][3]]],
      [3, 2, [3, Int(matGL3[1][1]), 4, Int(matGL3[2][1]), 5, Int(matGL3[3][1])]],
      [4, 2, [3, Int(matGL3[1][2]), 4, Int(matGL3[2][2]), 5, Int(matGL3[3][2])]],
      [5, 2, [3, Int(matGL3[1][3]), 4, Int(matGL3[2][3]), 5, Int(matGL3[3][3])]] ]);
    fi;
end;
###################################################################
SOTRec.NumberGroupsP4Q := function(p, q)
  local m;
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    if q = 2 then
      return 55;
    elif p = 2 and q = 3 then
      return 52;
    elif p = 2 and q <> 3 then
      return 14 + 28
                + 9*SOTRec.w((q - 1), 4)
                + 2*SOTRec.w((q - 1), 8)
                + SOTRec.w((q - 1), 16)
                + SOTRec.delta(5, q)
                + SOTRec.delta(7, q);
    elif p = 3 and q <> 2 then
      return 15 + 2*SOTRec.delta(13, q)
                + SOTRec.delta(5, q)
                + 34*SOTRec.w((q - 1), 3)
                + 11*SOTRec.w((q - 1), 9)
                + 2*SOTRec.w((q - 1), 27)
                + SOTRec.w((q - 1), 81);
    elif q = 3 and p <> 2 then
      return 15 + 54*SOTRec.w((p - 1), 3)
                + 6*SOTRec.w((p + 1), 3);
    else
      return 15 + SOTRec.w((q - 1), p)*(5*p + 19)
                + SOTRec.w((q - 1), p^2)*(2*p + 5)
                + SOTRec.w((q - 1), p^3)*2
                + SOTRec.w((q - 1), p^4)
                + SOTRec.w((p - 1), q)*1/24*(q^3 + 31*q^2 + 189*q + 423 + 16*SOTRec.w(q - 1, 3) + 12*SOTRec.w(q - 1, 4))
                + SOTRec.w((p + 1), q)*1/4*(q + 21 + 2*SOTRec.w(q - 1, 4))
                + SOTRec.w((p^2 + p + 1), q)
                + SOTRec.w((p^2 + 1), q) - SOTRec.delta(3, p)*SOTRec.w((p - 1), q);
    fi;
  end;

