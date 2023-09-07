##The following function identifies a group of order p^4q (p, q are distinct primes) by its SOT-group ID.
##This is under development and NOT part of the submitted manuscript

## Note that two split extensions C_q \ltimes_\phi P and C_q \ltimes_\psi P are isomorphic if and only if Im(\phi) and Im(\psi) are conjugate in Aut(P) (see [2, Proposition 3.6]).
  ## Moreover, we apply the following result (Lemma 9 in The enumeration of groups of order p^nq for n ≤ 5 by Eick & Moede):
  ## Theorem:
  ## Let p, q be distinct primes and let G, H be finite groups. If there exists a homomorphism \phi : G \to H such that Ker(\phi) is a p-group, then the number of conjugacy classes of subgroups of order q in G and in H coincide.

  ## This implies that if G is a finite group. Recall that O_p(G) (PCore(G) in GAP) is the largest normal p-subgroup of G. The natural projection \pi : G \to O_p(G) thus is a homomorphism with p-group kernel. It then follows that the number of conjugacy classes of subgroups of order q in G coincides with that in G/O_p(G).
    ## In particular, setting G \cong Aut(P), this shows that the number of isomorphism types of C_q \ltimes P for a given p-group P coincides with the number of conjugacy classes of subgroups of order q in Aut(P)/O_p(Aut(P)).
##########################################
SOTRec.IdGroupP4Q := function(group, n, fac)
  local p, q, flag, P, Q, Zen, zenp, gens, G, a, b, c, d, e, f, g, h, r1, r2, r3, r4, s1, s2, s3, s4 ,R1, R2, R3, R4, S1, S2, S3, S4,
        sc, fpc, idfp, pc, mat, matGL2, matGL3, matGL4, Idfunc, IdTuplei, i, j, k, l, m, s, t, u, v, w, x, y, z,
        exps1, exps2, pcgs, pcgsp, pcgsq, idP, g1, g2, g3, g4, g5, char, dP, dG,
        exp1, exp2, exp3, exp4, det, tmp, ev, evm, N1, N2,
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
        c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, data;
    p := fac[2][1];
    q := fac[1][1];
    ####
    Assert(1, p <> q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(p));
    ####
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
    P := SylowSubgroup(group, p);;
    Q := SylowSubgroup(group, q);;
    pcgsp := Pcgs(P);;
    pcgsq := Pcgs(Q);;
    Zen := Centre(group);;
    if p = 2 then
        idP := Position([ 1, 5, 2, 10, 14, 13, 11, 3, 12, 4, 6, 8, 7, 9 ], IdGroup(P)[2]);
    elif p = 3 then
        idP := Position([ 1, 5, 2, 11, 15, 14, 6, 13, 3, 4, 12, 8, 9, 7, 10 ], IdGroup(P)[2]);
    else
        idP := Position([ 1, 5, 2, 11, 15, 14, 6, 13, 3, 4, 12, 9, 10, 7, 8 ], IdGroup(P)[2]);
    fi;
    ####
    c0 := 15 - SOTRec.delta(2, p);
    c1 := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3) + SOTRec.w((q - 1), p^4);
    c2 := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), p^2) + SOTRec.w((q - 1), p^3);
    c3 := SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c4 := 2*SOTRec.w((q - 1), p) + SOTRec.w((q - 1), p^2);
    c5 := SOTRec.w((q - 1), p);
    c6 := 3*SOTRec.w((q - 1), p);
    c7 := (1 - SOTRec.delta(2, p))*(p*SOTRec.w((q - 1), p) + p*SOTRec.w((q - 1), p^2)) + 3*SOTRec.delta(2, p);
    c8 := (1 - SOTRec.delta(2, p))*(p + 1)*SOTRec.w((q - 1), p) + SOTRec.delta(2, p)*(2 + SOTRec.w((q - 1), 4));
    c9 := 2*SOTRec.w((q - 1), p) + (1 - SOTRec.delta(2, p))*SOTRec.w((q - 1), p^2);
    c10 := p*SOTRec.w((q - 1), p) + (p - 1)*SOTRec.w((q - 1), p^2);
    c11 := 2*SOTRec.w((q - 1), p) + 2*SOTRec.w((q - 1), 4)*SOTRec.delta(2, p);
    c12 := p*SOTRec.w((q - 1), p) + SOTRec.delta(2, p);
    c13 := p*SOTRec.w((q - 1), p) - SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    c14 := 2*SOTRec.w((q - 1), p) + SOTRec.delta(3, p)*SOTRec.w((q - 1), p);
    c15 := (1 - SOTRec.delta(2, p))*2*SOTRec.w((q - 1), p);
    c16 := SOTRec.w((p - 1), q);
    c17 := (q + 1)*SOTRec.w((p - 1), q);
    c18 := 1/2*(q + 3 - SOTRec.delta(2, q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    c19 := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q);
    c20 := 1/24*(q^3 + 7*q^2 + 21*q + 39 + 16*SOTRec.w((q - 1), 3) + 12*SOTRec.w((q - 1), 4))*SOTRec.w((p - 1), q)*(1 - SOTRec.delta(2, q)) + 4*SOTRec.delta(2, q)
        + 1/4*(q + 5 + 2*SOTRec.w((q - 1), 4))*SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q))
        + SOTRec.w((p^2 + p +1), q)*(1 - SOTRec.delta(3, q))
        + SOTRec.w((p^2 + 1), q)*(1 - SOTRec.delta(2, q));
    c21 := 1/2*(q + 3 - SOTRec.delta(2,q))*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q)*(1 - SOTRec.delta(2, q));
    c22 := SOTRec.w((p - 1), q);
    c23 := (q + 1)*SOTRec.w((p - 1), q);
    c24 := (q + 1)*SOTRec.w((p - 1), q) + SOTRec.delta(n, 3*2^4);;
    c25 := SOTRec.w((p - 1), q);
    c26 := (1/2*(q^2 + 2*q + 3)*SOTRec.w((p - 1), q) + SOTRec.w((p + 1), q))*(1 - SOTRec.delta(2,q)) + 5*SOTRec.delta(2, q) - SOTRec.delta(2, p);
    c27 := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    c28 := SOTRec.w((p - 1), q)*(1 + 2*SOTRec.delta(2, q));
    c29 := (q + 1)*SOTRec.w((p - 1), q);
    c30 := SOTRec.w((p - 1), q);
    ####
    Idfunc := function(q, l)
      local x, y, a, b, tuple, n, id;
        x := l[1] mod (q - 1);
        y := l[2] mod (q - 1);
        if l in [[(q-1)/3, 2*(q-1)/3], [2*(q-1)/3, (q-1)/3]] then
          return 1/6*(q^2 - 5*q + 6 + 4*SOTRec.w((q - 1), 3));
        else
          tuple := SortedList(Filtered(
          [SortedList([x, y]), SortedList([-x, y-x] mod (q - 1)), SortedList([-y, x-y] mod (q - 1))],
          list -> list[1] < Int((q + 2)/3) and list[2] < q - 1 - list[1]))[1];
          a := tuple[1];
          b := tuple[2];
          return Sum([1..a-1], x -> q - 1 - 3*x) + b + 1 - 2*a;
        fi;
    end;
    ####
    IdTuplei := function(q, l)
      local x, y, z, a, b, c, tuple, n, id;
        x := l[2] mod (q - 1);
        y := l[3] mod (q - 1);
        z := l[4] mod (q - 1);
        tuple := SortedList(Filtered(
        [SortedList([x, y, z]), SortedList([-x, y-x, z-x] mod (q - 1)), SortedList([-y, z-y, x-y] mod (q - 1)), SortedList([-z, x-z, y-z] mod (q - 1))],
        list -> list[1] < Int((q + 3)/4) and list[2] < q - 2*list[1]))[1];
        a := tuple[1];
        b := tuple[2];
        c := tuple[3];
        if tuple = [(q-1)/4, (q-1)/2, 3*(q-1)/4] then
          return 1/24*(q^3- 9*q^2+29*q-33 + 12*SOTRec.w((q - 1), 4));
        else
          id := Sum([1..a-1], x -> Sum([2*x..(q-1)/2], y -> q - 1 - 2*x - y) + Sum([(q+1)/2..q - 2 - 2*x], y -> q - 2 - 2*x - y));
          if b < (q + 1)/2 then
            id := id + Sum([2*a..b-1], x -> q - 1 - 2*a - x) + c - a - b + 1;
          else
            id := id + Sum([2*a..(q - 1)/2], x -> q - 1 - 2*a - x) + Sum([(q + 1)/2..(b - 1)], x -> q - 2 - 2*a - x) + c - a - b;
          fi;
        fi;
      return id;
    end;
    ####
    flag := [IsNormal(group, P), IsNormal(group, Q), DerivedSubgroup(group)];
    dG := flag[3];
    ####
    if IsNilpotent(group) then
      return [n, idP];
    elif flag{[1, 2]} = [false, true] then
      sc := Size(Zen);
      if idP = 1 then
        if sc = p^3 then
          return [n, c0 + 1];
        elif sc = p^2 then
          return [n, c0 + 2];
        elif sc = p then
          return [n, c0 + 3];
        elif sc = 1 then
          return [n, c0 + 4];
        fi;

      elif idP = 2 then
        if sc = p^3 then
          if IsCyclic(Zen) then
            return [n, c0 + c1 + 1];
          else
            return [n, c0 + c1 + 2];
          fi;
        elif sc = p^2 then
          if IsCyclic(Zen) then
            return [n, c0 + c1 + 3];
          else
            return [n, c0 + c1 + 4];
          fi;
        elif sc = p then
          return [n, c0 + c1 + 5];
        fi;

      elif idP = 3 then
        if sc = p^3 then
          return [n, c0 + c1 + c2 + 1];
        elif sc = p^2 then
          return [n, c0 + c1 + c2 + 2];
        fi;

      elif idP = 4 then
        if sc = p^3 then
          if Exponent(Zen) = p^2 then
            return [n, c0 + c1 + c2 + c3 + 1];
          else
            return [n, c0 + c1 + c2 + c3 + 2];
          fi;
        elif sc = p^2 then
          return [n, c0 + c1 + c2 + c3 + 3];
        fi;

      elif idP = 5 then
        return [n, c0 + c1 + c2 + c3 + c4 + 1];

      elif idP = 6 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if idfp[2] = 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + 1];
        elif idfp[2] = 3 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + 2];
        elif idfp[2] = 4 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + 3];
        fi;

      elif idP = 7 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[1] = p^3 then
            repeat g := Random(P); until not g in Zen and pcgsq[1]^g = pcgsq[1];
            if Order(g) = p^3 then
              repeat h := Random(P); until pcgsq[1]^h <> pcgsq[1] and h^g = h*g^(p^2);
              gens := [g, h, pcgsq[1], g^(p^2)];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              k := LogFFE(ExponentsOfPcElement(G, gens[3]^gens[2])[3] * One(GF(q)), r1) mod p;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + k];
            elif Order(g) < p^3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + p];
            fi;
          elif idfp[1] = p^2 then
            if idfp[2] = 1 then
              repeat g3 := Random(P); until Group([g3^p]) = Zen and pcgsq[1]^g3 = pcgsq[1];
              repeat g := Random(P); until Group([g^p]) = Centre(P) and g^(p^2) = g3^p;
              gens := [g, g^p, g3, g^(p^2), pcgsq[1]];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              x := Inverse(ExponentsOfPcElement(G, gens[3]^gens[1])[4]) mod p;
              k := LogFFE(ExponentsOfPcElement(G, gens[5]^(gens[2]^x))[5] * One(GF(q)), r1) mod p;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + p + k];
            elif idfp[2] = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + 2*p];
            fi;
          fi;
        elif p = 2 then
          if idfp[2] = 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + 1];
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + 2];
          elif idfp[2] = 5 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + 3];
          fi;
        fi;

      elif idP = 8 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[2] = 2 then
            repeat h := Random(P); until Group([h^p]) = DerivedSubgroup(P) and pcgsq[1]^h = pcgsq[1];
            repeat g := Random(P); until pcgsq[1]^g <> pcgsq[1] and h^g <> h^(p+1);
            repeat g4 := Random(P); until Group([h^p, g4]) = Zen;
            gens := [g, h, h^p, pcgsq[1], g4];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            x := Inverse(ExponentsOfPcElement(G, gens[2]^gens[1])[3]) mod p;
            k := LogFFE(ExponentsOfPcElement(G, gens[4]^(gens[1]^x))[4] * One(GF(q)), r1) mod p;
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + k];
          elif idfp[2] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + p];
          elif idfp[2] = 5 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + p + 1];
          fi;
        elif p = 2 then
          if idfp[1] = 8 then
            if idfp[2] = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + 1];
            elif idfp[2] = 5 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + 2];
            fi;
          elif idfp[1] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + 3];
          fi;
        fi;

      elif idP = 9 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[1] = p^3 then
            if idfp[2] = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + 1];
            elif idfp[2] = 5 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + 2];
            fi;
          elif idfp[1] = p^2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + 3];
          fi;
        elif p = 2 then
          if idfp[2] = 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + 1];
          elif idfp[2] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + 2];
          fi;
        fi;

      elif idP = 10 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[1] = p^3 then
            repeat h := Random(P); until not h in Zen and pcgsq[1]^h = pcgsq[1] and Order(h) = p^2;
              if Group([h^p]) <> DerivedSubgroup(P) then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 1];
              elif Group([h^p]) = DerivedSubgroup(P) then
                repeat g := Random(P); until pcgsq[1]^g <> pcgsq[1] and h^g = h^(p+1);
                gens := [g, h, h^p, pcgsq[1], g^p];
                G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
                x := Inverse(ExponentsOfPcElement(G, gens[2]^gens[1])[3]) mod p;
                k := LogFFE(ExponentsOfPcElement(G, gens[4]^(gens[1]^x))[4] * One(GF(q)), r1) mod p;
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 1 + k];
              fi;
          elif idfp[1] = p^2 then
            repeat h := Random(P); until Group([h^p]) = Zen and pcgsq[1]^h = pcgsq[1];
            repeat g := Random(P); until pcgsq[1]^g <> pcgsq[1] and h^g = h^(p+1);
            gens := [g, h, h^p, pcgsq[1], g^p];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            x := Inverse(ExponentsOfPcElement(G, gens[2]^gens[1])[3]) mod p;
            k := LogFFE(ExponentsOfPcElement(G, gens[4]^(gens[1]^x))[4] * One(GF(q)), r2) mod p;
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + p + k];
          fi;
        elif p = 2 then
          if idfp[1] = 8 then
            repeat g := Random(P); until Group([g^p, pcgsq[1]]) = flag[3];
            if pcgsq[1]^g <> pcgsq[1] then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 1];
            else
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 2];
            fi;
          elif idfp[1] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 3];
          fi;
        fi;

      elif idP = 11 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 1];
          elif idfp[2] = 5 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 2];
          fi;
        elif p = 2 then
          if idfp[1] = 8 then
            if idfp[2] = 1 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 1];
            elif idfp[2] = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 2];
            fi;
          elif idfp[1] = 4 then
            if idfp[2] = 1 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 3];
            elif idfp[2] = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + 4];
            fi;
          fi;
        fi;

      elif idP = 12 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[2] = 2 then
            repeat g4 := Random(P); until Group([g4, Pcgs(Zen)[1]]) = DerivedSubgroup(P);
            repeat g2 := Random(P); until Group([g2^p]) = Zen and g2^g4 = g2 and pcgsq[1]^g2 = pcgsq[1];
            repeat g1 := Random(P); until pcgsq[1]^g1 <> pcgsq[1] and Order(g1) = p and g4^g1 = g4*g2^p;
            gens := [g1, g2, g4, pcgsq[1], g2^p];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            x := RootMod(ExponentsOfPcElement(G, gens[2]^gens[1])[3], 2, p);
            k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(q)), r1^x) mod p;
            if k > (p - 1)/2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + p - k];
            else
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + k];
            fi;
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + (p + 1)/2];
          elif idfp[2] = 4 then
            if p > 3 then
              repeat g4 := Random(P); until Group([g4, Pcgs(Zen)[1]]) = DerivedSubgroup(P);
              repeat g2 := Random(P); until Group([g2^p]) = Zen and g2^g4 = g2 and pcgsq[1]^g2 = pcgsq[1]^R1;
              repeat g1 := Random(P); until pcgsq[1]^g1 <> pcgsq[1] and Order(g1) = p and g4^g1 = g4*g2^p;
              gens := [g1, g2, g4, pcgsq[1], g2^p];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              x := RootMod(ExponentsOfPcElement(G, gens[2]^gens[1])[3], 2, p);
              k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(q)), r1^x) mod p;
              if k > (p - 1)/2 then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + (p + 1)/2 + p - k];
              else
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + (p + 1)/2 + k];
              fi;
            elif p = 3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + (p + 1)/2 + 1];
            fi;
          fi;
        elif p = 2 then
          if idfp[2] = 1 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1];
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 2];
          elif idfp[2] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 3];
          fi;
        fi;

      elif idP = 13 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 3 then
          if idfp[2] = 2 then
            repeat g4 := Random(P); until Group([g4, Pcgs(Zen)[1]]) = DerivedSubgroup(P);
            repeat g2 := Random(P); until Group([g2^p]) = Zen and g2^g4 = g2 and pcgsq[1]^g2 = pcgsq[1];
            repeat g1 := Random(P); until pcgsq[1]^g1 <> pcgsq[1] and Order(g1) = p and g4^g1 = g4*g2^(Int(a)*p);
            gens := [g1, g2, g4, pcgsq[1], g2^p];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            x := RootMod(ExponentsOfPcElement(G, gens[2]^gens[1])[3], 2, p);
            k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(q)), r1^x) mod p;
            if k > (p - 1)/2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + p - k];
            else
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + k];
            fi;
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + (p + 1)/2];
          elif idfp[2] = 4 then
            repeat g4 := Random(P); until Group([g4, Pcgs(Zen)[1]]) = DerivedSubgroup(P);
            repeat g2 := Random(P); until Group([g2^p]) = Zen and g2^g4 = g2 and pcgsq[1]^g2 = pcgsq[1]^R1;
            repeat g1 := Random(P); until pcgsq[1]^g1 <> pcgsq[1] and Order(g1) = p and g4^g1 = g4*g2^(Int(a)*p);
            gens := [g1, g2, g4, pcgsq[1], g2^p];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            x := RootMod(ExponentsOfPcElement(G, gens[2]^gens[1])[3], 2, p);
            k := LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(q)), r1^x) mod p;
            if k > (p - 1)/2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + (p + 1)/2 + p - k];
            else
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + (p + 1)/2 + k];
            fi;
          fi;
        elif p = 3 then
          if idfp[2] = 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + 1];
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + 2];
          fi;
        else #p = 2
          if idfp[2] = 1 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + 1];
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + 2];
          fi;
        fi;

      elif idP = 14 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 2 then
          if idfp[2] = 5 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + 1];
          elif idfp[2] = 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + 2];
          elif idfp[1] = 27 and idfp[2] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + 2 + SOTRec.delta(3, p)];
          fi;
        elif p = 2 then
          if idfp[2] = 1 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + 1];
          elif idfp[2] = 4 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + 2];
          fi;
        fi;

      elif idP = 15 then
        f := FittingSubgroup(group);
        idfp := IdGroup(SylowSubgroup(f, p));
        if p > 3 and idfp[2] = 5 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + 1];
        elif p > 3 and idfp[2] = 4 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + 2];
        elif p = 3 and idfp[2] = 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + 1];
        elif p = 3 and idfp[2] = 4 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + 2];
        fi;
      fi;

    elif flag{[1, 2]} = [true, false] then
      sc := Size(Zen);
      f := FrattiniSubgroup(group);
      if idP = 1 then
        return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + 1];

      elif idP = 2 then
        if sc = p then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + 1];
        elif sc = p^3 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + 2];
        elif sc = 1 then
          repeat g := Random(P); until Order(g) = p^3 and Group([g^p]) = f;
          repeat h := Random(P); until Order(h) = p and Group([g, h]) = P;
          gens := [pcgsq[1], g, g^p, g^(p^2), h];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
          x := Inverse(LogMod(ExponentsOfPcElement(G, gens[4]^gens[1])[4], Int(s3), p)) mod q;
          k := LogFFE(ExponentsOfPcElement(G, gens[5]^gens[1])[5]^x*One(GF(p)), s1) mod q;
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + 2 + k];
        fi;

      elif idP = 3 then
        if sc = p^2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + 1];
        elif sc = 1 and (p - 1) mod q = 0 then
          pc := Pcgs(f);
          gens := [pcgsq[1], pc[1], pc[2]];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
          exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
          exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
          matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}]*One(GF(p));
          ev := SortedList(List(Eigenvalues(GF(p), matGL2), x -> LogFFE(LogMod(Int(x), S2, p)*One(GF(q)), b)));
          if Length(ev) = 1 then
            k := 0;
          else
            k := ev[2] - ev[1];
            if k > (q - 1)/2 then
              k := (q - 1) - k;
            fi;
          fi;
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + 1 + (k + 1)];
        elif sc = 1 and (p + 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + 1];
        fi;

      elif idP = 4 then
        if (p - 1) mod q = 0 then
          if sc = p^3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + 1];
          elif sc = p^2 then
            if IsCyclic(Zen) then
              group := group/Zen;
              pcgsq := Pcgs(SylowSubgroup(group, q));
              pcgsp := Pcgs(SylowSubgroup(group, p));
              gens := [pcgsq[1]];
              Append(gens, pcgsp);
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
              exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
              matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}] * One(GF(p));
              ev := SortedList(List(Eigenvalues(GF(p), matGL2), x -> LogFFE(LogFFE(x, s1)*One(GF(q)), b)));
              if Length(ev) = 1 then
                k := 0;
              else
                k := ev[2] - ev[1];
                if k > (q - 1)/2 then
                  k := (q - 1) - k;
                fi;
              fi;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + 1 + (k + 1)];
            elif not IsCyclic(Zen) then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + 1 + Int((q + 3)/2)];
            fi;
          elif sc = p then
            group := group/Zen;
            P := SylowSubgroup(group, p);
            Q := SylowSubgroup(group, q);
            repeat g := Random(P); until Order(g) = p and not g in FrattiniSubgroup(P);
            h := Filtered(Pcgs(P), x -> Order(x) = p^2)[1];
            gens:= [Pcgs(Q)[1], g, h, h^p];
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            x := Inverse(LogMod(ExponentsOfPcElement(G, gens[4]^gens[1])[4], Int(s2), p)) mod q;
            k := LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2]^x*One(GF(p)), s1) mod q;
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + 1 + Int((q + 3)/2) + k];
          elif sc = 1 then
            repeat g4 := Random(P); until Order(g4) = p^2 and Group([g4^p]) = f;
            repeat g3 := Random(P); until Order(g3) = p and not g3 in f;
            repeat g := Random(P); until Order(g) = p and Group([g, g3, g4, g4^p]) = P;
            gens := [pcgsq[1], g, g3, g4, g4^p];;
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}] * One(GF(p));
            x := Inverse(LogMod(ExponentsOfPcElement(G, gens[5]^gens[1])[5], Int(s2), p)) mod q;
            evm := Eigenvalues(GF(p), matGL2^x);
            if Length(evm) > 1 then
              evm := SortedList(List(evm, x -> LogFFE(x, s1)));
              k := evm[1];
              l := evm[2];
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + Int((q + 5)/2) + (q - 1)
                        + (k - 1)*(2*q - 2 - k)/2 + l - k];
            elif Length(evm) = 1 then
              k := List(evm, x -> LogFFE(x, s1))[1];
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + Int((q + 5)/2) + (q - 1)
                        + (q^2 - 3*q + 2)/2 + k];
            fi;
          fi;
        elif (p + 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + 1];
        fi;

      elif idP = 5 then
        if sc = p^3 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                  + c18 + c19 + 1];
        elif sc = p^2 then
          if (p - 1) mod q = 0 then
            gens:= [pcgsq[1]];
            Append(gens, Filtered(pcgsp, x -> not x in Zen));
            Append(gens, Filtered(pcgsp, x -> x in Zen));
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            matGL2 := [exp1{[2, 3]}, exp2{[2, 3]}]* One(GF(p));
            det := DeterminantMat(matGL2);
            x := Inverse(LogFFE(Eigenvalues(GF(p), matGL2)[1], s1)) mod q;
            det := LogFFE((LogFFE(det^x, s1) - 1)*One(GF(q)), b) mod (q - 1);
            if det < Int((q + 1)/2) then
              k := det;
            else
              k := (q - 1) - det;
            fi;
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                      + c18 + c19 + 1 + k + 1];
          elif (p + 1) mod q = 0 and q > 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                    + c18 + c19 + 1];
          fi;
        elif sc = p then
          if (p - 1) mod q = 0 then
            gens:= [pcgsq[1]];
            Append(gens, Filtered(pcgsp, x -> not x in Zen));
            Append(gens, Filtered(pcgsp, x -> x in Zen));
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            mat := [exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}] * One(GF(p));
            ev := Eigenvalues(GF(p), mat);
            if q = 3 then
              if Length(ev) = 1 then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                          + c18 + c19 + 1 + Int((q + 1)/2) + 1];
              else
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                          + c18 + c19 + 1 + Int((q + 1)/2) + 2];
              fi;
            elif q > 3 then
              if Length(ev) = 1 then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                          + c18 + c19 + 1 + Int((q + 1)/2) + 1];
              elif Length(ev) = 2 then
                evm := SOTRec.EigenvaluesWithMultiplicitiesGL3P(mat, p);
                x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
                k := LogFFE(Filtered(evm, x -> x[2] = 1)[1][1]^x, s1) mod q;
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                                          + c18 + c19 + Int((q + 5)/2) + k - 1];
              elif Length(ev) = 3 then
                x := Inverse(LogFFE(Eigenvalues(GF(p), mat)[1], s1)) mod q;
                l := List(ev, i -> i^x);
                y := List(Filtered(l, x->x <> s1), x -> LogFFE(x, s1)*One(GF(q)));
                l := List(y, x -> (LogFFE(x, b) mod (q - 1)));
                k := Idfunc(q, l);
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                             + c18 + c19 + Int((q + 1)/2) + q + k];
              fi;
            elif q = 2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                          + c18 + c19 + 3];
            fi;
          elif (p^2 + p + 1) mod q = 0 and q > 3 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                          + c18 + c19 + 1];
          fi;
        elif sc = 1 then
          if q = 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                          + c18 + c19 + 4];
          elif (p - 1) mod q = 0 then
            gens:= [pcgsq[1]];
            Append(gens, pcgsp);;
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);;
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);;
            exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);;
            exp4 := ExponentsOfPcElement(G, gens[5]^gens[1]);;
            mat := [exp1{[2, 3, 4, 5]}, exp2{[2, 3, 4, 5]}, exp3{[2, 3, 4, 5]}, exp4{[2, 3, 4, 5]}] * One(GF(p));;
            evm := SOTRec.EigenvaluesWithMultiplicitiesGL4P(mat, p);
            if List(evm, x -> x[2]) = [4] then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                          + c18 + c19 + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + 1];
            elif List(evm, x -> x[2]) = [1, 3] then
              x := Inverse(LogFFE(evm[2][1], s1)) mod q;
              k := LogFFE(LogFFE(evm[1][1]^x, s1) * One(GF(q)), b) mod (q - 1);
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15
                      + c16 + c17 + c18 + c19
                      + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + k + 1];
            elif List(evm, x -> x[2]) = [2, 2] then
              evm := SortedList(List(evm, x -> LogFFE(LogFFE(x[1], s1) * One(GF(q)), b)));
              k := evm[2] - evm[1];
              if k > (q - 1)/2 then
                k := q - 1 - k;
              fi;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15
                      + c16 + c17 + c18 + c19
                      + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + q - 1 + k];
            elif List(evm, x -> x[2]) = [1, 1, 2] then
              x := Inverse(LogFFE(Filtered(evm, x -> x[2] = 2)[1][1], s1)) mod q;
              k := LogFFE(LogFFE(Filtered(evm, x -> x[2] = 1)[1][1]^x, s1)*One(GF(q)), b) mod (q - 1);
              l := LogFFE(LogFFE(Filtered(evm, x -> x[2] = 1)[2][1]^x, s1)*One(GF(q)), b) mod (q - 1);
              if l > k then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15
                      + c16 + c17 + c18 + c19
                      + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + q - 1 + Int(q - 1)/2 + (2*q - 4 - k)*(k - 1)/2 + l - k];
              elif k > l then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15
                      + c16 + c17 + c18 + c19
                      + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + q - 1 + Int(q - 1)/2 + (2*q - 4 - l)*(l - 1)/2 + k - l];
              fi;
            elif List(evm, x -> x[2]) = [1, 1, 1, 1] then
              x := LogFFE(evm[1][1], s1) mod q;
              l := SortedList(List(evm, i -> LogFFE(LogFFE(i[1], s1^x) * One(GF(q)), b) mod (q - 1)));
              k := IdTuplei(q, l);
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15
                      + c16 + c17 + c18 + c19
                      + 1/6*(q^2 + 4*q + 9 + 4*SOTRec.w((q - 1), 3) - 3*SOTRec.delta(2, q)) + q - 1 + Int(q - 1)/2 + (q - 2)*(q - 3)/2 + k];
            fi;
          elif (p + 1) mod q = 0 and q > 2 then
            gens:= [pcgsq[1]];
            Append(gens, pcgsp);
            G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
            exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
            exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
            exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
            exp4 := ExponentsOfPcElement(G, gens[5]^gens[1]);
            mat := [exp1{[2, 3, 4, 5]}, exp2{[2, 3, 4, 5]}, exp3{[2, 3, 4, 5]}, exp4{[2, 3, 4, 5]}] * One(GF(p^2));
            evm := SOTRec.EigenvaluesGL4P2(mat, p);
            s := PrimitiveElement(GF(p^2));
            t := s^((p^2-1)/q);
            x := Inverse(LogFFE(evm[1][1], t)) mod q;
            y := LogFFE(LogFFE(evm[2][1]^x, t) * One(GF(q)), b) mod (q - 1);
            if y > Int(3*(q - 1)/4) then
              k := q - 1 - y;
            elif y > (q - 1)/2 then
              k := y - (q - 1)/2;
            elif y > Int((q - 1)/4) then
              k := (q - 1)/2 - y;
            else
              k := y;
            fi;
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + 1 + k + 1];
          elif (p^2 + 1) mod q = 0 and q > 2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + 1];
          fi;
        fi;

      elif idP = 6 then
        if (p - 1) mod q = 0 then
          if sc = p^2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + 1];
          elif sc = 1 then
            if Size(flag[3]) = p^3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + 2];
            elif Size(flag[3]) = p^4 then
              zenp := Centre(P);
              repeat g2 := Random(zenp); until Group([g2]) = zenp;
              g := Filtered(Pcgs(dG), x -> not x in zenp)[1];
              repeat h := Random(dG); until h^g <> h;
              gens := [pcgsq[1], g, g2, g2^p, h];;
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
              exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
              exp2 := ExponentsOfPcElement(G, gens[5]^gens[1]);
              mat := [exp1{[2, 5]}, exp2{[2, 5]}] * One(GF(p));
              evm := Eigenvalues(GF(p), mat);
              if Length(evm) = 1 then
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + 2 + Int((q - 1)/2)];
              else
                k := SortedList([Inverse(LogFFE(evm[2], evm[1]) + 1) mod q, Inverse(LogFFE(evm[1], evm[2]) + 1) mod q]);
                k := Filtered(k, x-> x > 1 and x < (q + 3)/2)[1];
                return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                       + c18 + c19 + c20 + 2 + k - 1];
              fi;
            fi;
          fi;
        elif (p + 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                  + c18 + c19 + c20 + 1];
        fi;

      elif idP = 7 then
        return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                + c18 + c19 + c20 + c21 + 1];

      elif idP = 8 then
        if sc = p then
          if IsCyclic(flag[3]) then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + 2];
          else
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + 1];
          fi;
        elif sc = 1 then
          zenp := Centre(P);
          repeat g := Random(flag[3]); until Group([g^p]) = f;
          repeat h := Random(flag[3]); until Order(h) = p and not h in f;;
          gens := [pcgsq[1], h, g, g^p];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogMod(ExponentsOfPcElement(G, gens[4]^gens[1])[4], Int(s2), p)) mod q;
          k := LogFFE(ExponentsOfPcElement(G, gens[2]^(gens[1]^x))[2] * One(GF(p)), s1);
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + 2 + k];
        fi;

      elif idP = 9 then
        if (p - 1) mod q = 0 then
          if sc = p then
            if Size(flag[3]) = p^2 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + 1];
            elif Size(flag[3]) = p^4 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + 2];
            fi;
          elif sc = 1 then
            zenp := Centre(P);
            if Size(flag[3]) = p^4 then
              repeat g := Random(P); until Order(g) = p and not g in zenp;
              h := Filtered(pcgsp, x -> Order(x) = p^2 and x^p in f)[1];
              gens := [pcgsq[1], g, Pcgs(DerivedSubgroup(P))[1], h, h^p];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
              x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[2]^gens[1])[2] * One(GF(p)), s1)) mod q;
              k := LogFFE(ExponentsOfPcElement(G, gens[3]^(gens[1]^x))[3] * One(GF(p)), s1) - 1;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + 2 + k];
            elif Size(flag[3]) = p^3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + c24];
            fi;
          fi;
        elif n = 48 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                  + c18 + c19 + c20 + c21 + c22 + c23 + 1];
        fi;

      elif idP = 10 then
        return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                + c18 + c19 + c20 + c21 + c22 + c23 + c24 + 1];

      elif idP = 11 then
        if (p - 1) mod q = 0 then
          if sc = p^2 then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 1];
          elif sc = p then
            zenp := Centre(P);
            if Size(flag[3]) = p^2 and flag[3] = zenp then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 2];
            elif Size(flag[3]) = p^2 and flag[3] <> zenp then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 3];
            elif Size(flag[3]) = p^3 then
              group := group/Zen;
              P := SylowSubgroup(group, p);
              Q := SylowSubgroup(group, q);
              pcgsp := Pcgs(P);
              pcgsq := Pcgs(Q);
              zenp := Centre(P);
              repeat g4 := Random(zenp); until Group([g4]) = zenp;
              g3 := Filtered(pcgsp, x -> not x in zenp)[1];
              repeat g2 := Random(P); until g3^g2 = g3*g4;
              gens := [pcgsq[1], g2, g3, g4];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
              exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);
              exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);
              exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);
              x := Inverse(LogFFE(exp3[4] * One(GF(p)), s1)) mod q;
              matGL3 := ([exp1{[2, 3, 4]}, exp2{[2, 3, 4]}, exp3{[2, 3, 4]}])^x * One(GF(p));
              k := List(Filtered(Eigenvalues(GF(p), matGL3), x -> x <> s1), x -> LogFFE(x, s1) mod q)[1];
              if k > (q + 1)/2 then
                k := q + 1 - k;
              fi;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 3 + k - 1];
            elif Size(flag[3]) = p^4 and q > 2 then
              zenp := Centre(P);
              repeat g4 := Random(zenp); until Group([g4]) = Zen;
              repeat g5 := Random(zenp); until Group([g4, g5]) = zenp;
              g3 := Filtered(pcgsp, x -> not x in zenp)[1];
              repeat g2 := Random(P); until g3^g2 = g3*g4;
              gens := [pcgsq[1], g2, g3, g4, g5];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);;
              exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);;
              exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);;
              exp4 := ExponentsOfPcElement(G, gens[5]^gens[1]);;
              matGL2 := [exp3{[4, 5]}, exp4{[4, 5]}] * One(GF(p));;
              ev := Eigenvalues(GF(p), matGL2);
              mat := [exp1{[2, 3, 4, 5]}, exp2{[2, 3, 4, 5]}, exp3{[2, 3, 4, 5]}, exp4{[2, 3, 4, 5]}] * One(GF(p));;
              evm := SOTRec.EigenvaluesWithMultiplicitiesGL4P(mat, p);
              if Length(evm) = 2 then
                k := (q - 1)/2;
              else
                x := Inverse(LogFFE(Filtered(List(evm, x->x[1]), x -> not x in ev)[1], s1)) mod q;
                k := LogFFE(Filtered(ev, x -> x <> Z(p)^0)[1]^x, s1);
                if k > (q - 1)/2 then
                  k := q - k;
                fi;
              fi;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 3 + (q - 1)/2 + k];
           elif Size(flag[3]) = p^4 and q = 2 then
             return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                     + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26];
            fi;
          elif sc = 1 then
            zenp := Centre(P);
            if Size(flag[3]) = p^3 then
              repeat g4 := Random(zenp); until Group([g4]) = DerivedSubgroup(P);
              repeat g5 := Random(zenp); until Group([g4, g5]) = zenp;
              repeat g3 := Random(P); until not g3 in zenp;
              repeat g2 := Random(P); until g3^g2 = g3*g4;
              gens := [pcgsq[1], g2, g3, g4, g5];
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
              x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(p)), s1)) mod q;
              k := LogFFE(ExponentsOfPcElement(G, gens[5]^(gens[1]^x))[5] * One(GF(p)), s1);
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 3 + (q - 1)*(1 - SOTRec.delta(2, q)) + k];
            elif Size(flag[3]) = p^4 then
              repeat g4 := Random(zenp); until Group([g4]) = DerivedSubgroup(P);
              repeat g5 := Random(zenp); until Group([g4, g5]) = zenp;
              g3 := Filtered(pcgsp, x -> not x in zenp)[1];
              repeat g2 := Random(P); until g3^g2 = g3*g4;
              gens := [pcgsq[1], g2, g3, g4, g5];;
              G := PcgsByPcSequence(FamilyObj(gens[1]), gens);;
              exp1 := ExponentsOfPcElement(G, gens[2]^gens[1]);;
              exp2 := ExponentsOfPcElement(G, gens[3]^gens[1]);;
              exp3 := ExponentsOfPcElement(G, gens[4]^gens[1]);;
              exp4 := ExponentsOfPcElement(G, gens[5]^gens[1]);;
              matGL2 := [exp3{[4, 5]}, exp4{[4, 5]}] * One(GF(p));
              mat := [exp1{[2, 3, 4, 5]}, exp2{[2, 3, 4, 5]}, exp3{[2, 3, 4, 5]}, exp4{[2, 3, 4, 5]}] * One(GF(p));;
              ev := Eigenvalues(GF(p), matGL2);
              if Length(ev) = 2 then
                y := ExponentsOfPcElement(G, gens[4]^gens[1])[4] * One(GF(p));;
                z := Filtered(ev, i -> i <> y)[1];;
                evm := SOTRec.EigenvaluesWithMultiplicitiesGL4P(mat, p);
                if List(evm, x -> x[2]) = [1, 3] then
                  if y = evm[1][1] and z = evm[2][1] then
                    k := 1;
                    l := 0;
                  fi;
                elif List(evm, x -> x[2]) = [1, 1, 2] then
                  if z = evm[3][1] then
                    x := LogFFE(Filtered(List(evm, x -> x[1]), x -> x <> y and x <> z)[1], s1);
                    l := LogFFE((LogFFE(y, s1^x) - 1) * One(GF(q)), b) mod (q - 1);
                    if l > (q - 3)/2 then
                      x := LogFFE(evm[3][1], s1);
                      l := LogFFE((LogFFE(y, s1^x) - 1) * One(GF(q)), b) mod (q - 1);
                    fi;
                    k := LogFFE(z * One(GF(p)), s1^x) mod q;
                  elif (y = evm[1][1] and z = evm[2][1]) or (y = evm[2][1] and z = evm[1][1]) then
                    x := Inverse(LogFFE(evm[3][1], s1)) mod q;
                    l := LogFFE((LogFFE(y^x, s1) - 1) * One(GF(q)), b) mod (q - 1);
                    if l > (q - 3)/2 then
                      l := q - 1 - l;
                    fi;
                    k := LogFFE((z * One(GF(p)))^x, s1);
                  fi;
                elif List(evm, x -> x[2]) = [1, 1, 1, 1] then
                  x := LogFFE(Filtered(List(evm, x -> x[1]), x -> x <> y and x <> z)[1], s1);
                  l := LogFFE((LogFFE(y, s1^x) - 1) * One(GF(q)), b) mod (q - 1);
                  if l > (q - 3)/2 then
                    x := LogFFE(Filtered(List(evm, x -> x[1]), x -> x <> y and x <> z)[2], s1);
                    l := LogFFE((LogFFE(y, s1^x) - 1) * One(GF(q)), b) mod (q - 1);
                  fi;
                  k := LogFFE(z * One(GF(p)), s1^x) mod q;
                  return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                              + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + ((2*q + 1) + (q - 1)/2*(k - 1) + l + 1)*(1 - SOTRec.delta(2, q)) + 2*SOTRec.delta(2, q)];
                fi;
              elif Length(ev) = 1 then
                y := ev[1];
                z := y;
                evm := SOTRec.EigenvaluesWithMultiplicitiesGL4P(mat, p);
                if List(evm, x -> x[2]) = [2, 2] then
                  x := Inverse(LogFFE(Filtered(List(evm, x -> x[1]), x -> x <> y)[1], s1)) mod q;
                  l := LogFFE((LogFFE(y^x, s1) - 1) * One(GF(q)), b) mod (q - 1);
                  if l > (q - 3)/2 then
                    l := q - 1 - l;
                  fi;
                  k := LogFFE((z * One(GF(p)))^x, s1);
                elif List(evm, x -> x[2]) = [1, 1, 2] then
                  x := Inverse(LogFFE(evm[1][1], s1)) mod q;
                  l := LogFFE((LogFFE(y^x, s1) - 1) * One(GF(q)), b) mod (q - 1);
                  if l > (q - 3)/2 then
                    x := Inverse(LogFFE(evm[2][1], s1)) mod q;
                    l := LogFFE((LogFFE(y^x, s1) - 1) * One(GF(q)), b) mod (q - 1);
                  fi;
                  k := LogFFE((z * One(GF(p)))^x, s1);
                fi;
              fi;
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + ((2*q + 1) + (q - 1)/2*(k - 1) + l + 1)*(1 - SOTRec.delta(2, q)) + 2*SOTRec.delta(2, q)];
            fi;
          fi;
        elif (p + 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                  + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + 1];
        fi;

      elif idP = 12 then
        if (p - 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + 1];
        elif q = 2 then
          if sc = p then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + 1];
          elif sc = 1 then
            if Size(flag[3]) = p^3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + 2];
            elif Size(flag[3]) = p^4 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + 3];
            fi;
          fi;
        fi;

      elif idP = 13 then
        if (p - 1) mod q = 0 and q > 2 then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + 1];
        elif q = 2 then
          if sc = p then
            return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                      + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + 1];
          elif sc = 1 then
            if Size(flag[3]) = p^3 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + 2];
            elif Size(flag[3]) = p^4 then
              return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                        + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + 3];
            fi;
          fi;
        fi;

      elif idP = 14 then
        if sc = p then
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                  + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + c28 + 1];
        elif sc = 1 then
          zenp := Centre(P);
          dP := DerivedSubgroup(P);
          repeat g := Random(dP); until Group([g, Pcgs(zenp)[1]]) = dP;
          repeat h := Random(P); until not h in dP and g^h = g;
          repeat g2 := Random(P); until not g2 in dP and g^g2 <> g;
          gens := [pcgsq[1], g2, Pcgs(zenp)[1], g, h];
          G := PcgsByPcSequence(FamilyObj(gens[1]), gens);
          x := Inverse(LogFFE(ExponentsOfPcElement(G, gens[3]^gens[1])[3] * One(GF(p)), s1)) mod q;
          k := LogFFE(ExponentsOfPcElement(G, gens[2]^(gens[1]^x))[2] * One(GF(p)), s1);
          return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                    + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + c28 + 2 + k];
        fi;

      elif idP = 15 then
        return [n, c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17
                + c18 + c19 + c20 + c21 + c22 + c23 + c24 + c25 + c26 + c27 + c28 + c29 + c30];
      fi;
    elif flag{[1, 2]} = [false, false] then
      f := FrattiniSubgroup(group);
      if n = 48 then
        if Size(f) = 1 then
          return [48, 49];
        elif Size(f) = 2 and Size(dG) = 12 then
          return [48, 50];
        elif Size(f) = 2 and Size(dG) = 24 then
          repeat g := Random(P); until Order(g) < 8 and not g in dG and not g in Zen;
          if Order(g) = 2 then
            return [48, 51];
          else
            return [48, 52];
          fi;
        fi;
      elif n = 1053 then
        return [n, 51];
      fi;
    fi;
end;
