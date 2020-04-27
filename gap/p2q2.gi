


############################################################################
msg.QthRootGL2P := function(p, q)
	local a, b;
	if not Gcd(p,q)=1 or not (p^2-1) mod q = 0 then
	 Error("Arguments has to be primes p, q, where q divides (p^2 - 1).\n");
	 else
	 a := PrimitiveElement(GF(p^2));
	 b := a^((p^2-1)/q);
	fi;
   return [ [0, 1], [-b^(p+1), b+b^p] ] * One(GF(p));
end;
####
############################################################################
msg.QsquaredthRootGL2P := function(p, q)
	local a, b;
	if not Gcd(p,q)=1 or not (p^2-1) mod (q^2) = 0 then
	 Error("Arguments has to be primes p, q, where q^2 divides (p^2 - 1).\n");
	 else
	 a := PrimitiveElement(GF(p^2));
	 b := a^((p^2-1)/(q^2));
	fi;
   return [ [0, 1], [-b^(p+1), b+b^p] ] * One(GF(p));
end;
####


############################################################################ all groups P2Q2
InstallGlobalFunction( allGroupsP2Q2, function(n)
  local fac, p, q, case0, case1, case2, case3, case4, case5, case6, case7, s;
    fac := Factors(n);
		## check input
    if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
      Error("Argument has to be of the form p^2*q^2, where p, q are primes");
		fi;

    q := fac[1];
    p := fac[4];
    s := [];
    Add(s, AbelianGroup([n]));
    Add(s, AbelianGroup([p, p*q^2]));
    Add(s, AbelianGroup([p^2*q, q]));
    Add(s, AbelianGroup([p, p*q, q]));

    ####place holder: case0: n = 36

    #### case1: q nmid (p-1), q nmid (p^2 -1), q neq 2
    if not (p^2 - 1) mod q = 0 then
    	return s;
		fi;

		    #### case2: q mid (p - 1), q^2 nmid (p^2 - 1)
		    case2 := function(p, q)
		      local t, i, G1, G2, G3, G4, G5, G6, G7, list;
		        list := [];
						if not (p - 1) mod q = 0 then return list; else
		        ##G1 semidirect product of C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
		          G1 := function(p, q) #refined
		            local a, b, coll, r, qq, ii, G;
		            ## get primitive root mod p^2
		              a := ZmodnZObj(Int(Z(p)),p^2);
		              if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
		              r := Int(b^(p*(p-1)/q));
		              coll := FromTheLeftCollector(4);
		              SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		              SetRelativeOrder(coll, 3, p);
		              SetRelativeOrder(coll, 4, p);
		              SetPower(coll, 1, [2, 1]);
		              SetPower(coll, 3, [4, 1]);
		              ## write g_2^{g_1} = g_2^a as g_2^{ii}g_3^{qq} where a = qq*p+ii (div with remainder)
		                ii := r mod p;
		                qq := (r - ii)/p;
		              SetConjugate(coll, 3, 1, [3, ii, 4, qq]);
		              SetConjugate(coll, 4, 1, [4, ii]);
		              G := PcpGroupByCollector(coll);
		              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		            end;
		          ##
		          Add(list, G1(p, q));
		          ##
		          ##G2 semidirect product of C_q^2 \ltimes C_{p^2}, \phi(Q) = C_q
		            G2 := function(p, q) #refined
		              local a, b, coll, r, qq, ii, G;
		              ## get primitive root mod p^2
		              a := ZmodnZObj(Int(Z(p)),p^2);
		                if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
		                r := Int(b^(p*(p-1)/q));
		                coll := FromTheLeftCollector(4);
		                SetRelativeOrder(coll, 1, q);
		                SetRelativeOrder(coll, 2, q);
		                SetRelativeOrder(coll, 3, p);
		                SetRelativeOrder(coll, 4, p);
		                SetPower(coll, 3, [4, 1]);
		                ## write g_2^{g_1} = g_2^a as g_2^{ii}g_3^{qq} where a = qq*p+ii (div with remainder)
		                  ii := r mod p;
		                  qq := (r - ii)/p;
		                SetConjugate(coll, 3, 1, [3, ii, 4, qq]);
		                SetConjugate(coll, 4, 1, [4, ii]);
		                G := PcpGroupByCollector(coll);
		                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		              end;
		          ##
		          Add(list, G2(p, q));
		          ##
		          ##G3 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
		          G3 := function(p, q) #refined
		            local coll, c, r, G;
		              c := Z(p);
		              r := Int(c^((p-1)/q));
		              coll := FromTheLeftCollector(4);
		              SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		              SetRelativeOrder(coll, 3, p);
		              SetRelativeOrder(coll, 4, p);
		              SetPower(coll, 1, [2, 1]);
		              SetConjugate(coll, 3, 1, [3, r]);
		              G := PcpGroupByCollector(coll);
		              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		            end;
		          ##
		          Add(list, G3(p, q));
		          ##
		          ##G4 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
		          G4 := function(i, p, q) #refined
		          	local coll, c, r, l, j, k, G;
		          		c := Z(p);
		          		r := Int(c^((p-1)/q));
		              l := Z(q);
		          		k := Int(l^i);
		          		j := Int((c^((p-1)/q))^k);
		          		coll := FromTheLeftCollector(4);
		          		SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		          		SetRelativeOrder(coll, 3, p);
		          		SetRelativeOrder(coll, 4, p);
		              SetPower(coll, 1, [2,1]);
		          		SetConjugate(coll, 3, 1, [3, r]);
		          		SetConjugate(coll, 4, 1, [4, j]);
		          		G := PcpGroupByCollector(coll);
		          		return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		          	end;
		          ##
							if (p - 1) mod q = 0 and q mod 2 = 1 then
		          t := (q-1)/2;
							else t := 0;
							fi;

		          for i in [0..t] do Add(list, G4(i, p, q)); od;
		          ##
		          ##G5 direct product of C_{qp} and semidirect product: C_q \times (C_q \ltimes C_p) \times C_p, \phi(Q) = C_q
		          G5 := function(p, q) #refined
		            local coll, c, r, G;
		              c := Z(p);
		              r := Int(c^((p-1)/q));
		              coll := FromTheLeftCollector(4);
		              SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		              SetRelativeOrder(coll, 3, p);
		              SetRelativeOrder(coll, 4, p);
		              SetConjugate(coll, 3, 1, [3, r]);
		              G := PcpGroupByCollector(coll);
		              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		            end;
		          ##
		          Add(list, G5(p, q));
		          ##
		          ##G6 direct products of C_q and semidirect product: C_q \times (C_q \ltimes C_p^2), \phi(Q) = C_q
		          G6 := function(i, p, q) #refined
		          	local coll, c, r, l, j, k, G;
		          		c:= Z(p);
		          		r:= Int(c^((p-1)/q));
		              l:= Z(q);
		          		k:= Int(l^i);
		          		j:= Int((c^((p-1)/q))^k);
		          		coll := FromTheLeftCollector(4);
		          		SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		          		SetRelativeOrder(coll, 3, p);
		          		SetRelativeOrder(coll, 4, p);
		          		SetConjugate(coll, 3, 1, [3, r]);
		          		SetConjugate(coll, 4, 1, [4, j]);
		          		G := PcpGroupByCollector(coll);
		          		return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		          	end;
		          ##
							if (p - 1) mod q = 0 and q mod 2 = 1 then
		          t := (q-1)/2;
							else t := 0;
							fi;

		          for i in [0..t] do Add(list, G6(i, p, q)); od;

		          ##
		          ##G7 semidirect product ((C_q \times C_q) \ltimes C_p) \times C_p, \phi(Q) = C_q^2
		          G7 := function(p, q) #refined
		            local coll, c, r, G;
		              c := Z(p);
		              r := Int(c^((p-1)/q));
		              coll := FromTheLeftCollector(4);
		              SetRelativeOrder(coll, 1, q);
		              SetRelativeOrder(coll, 2, q);
		              SetRelativeOrder(coll, 3, p);
		              SetRelativeOrder(coll, 4, p);
		              SetConjugate(coll, 3, 1, [3, r]);
		              SetConjugate(coll, 4, 2, [4, r]);
		              G := PcpGroupByCollector(coll);
		              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		            end;

		          ##
		          Add(list, G7(p, q));
		          ##
							fi;
		          return list;
		      end;
		    if (p - 1) mod q = 0 then
		    	Append(s, case2(p, q));
				fi;
		        ####
        #### case3: q mid (p + 1), q^2 nmid (p^2 - 1), q neq 2
        case3 := function(p, q)
          local G1, G2;
            ##G1 direct product of C_q and semidirect product: C_q \times (C_q \ltimes C_p^2)
            G1 := function(p, q) #refined
              local mat, G, coll;
        		  mat := msg.QthRootGL2P(p, q);
        		  coll := FromTheLeftCollector(4);
        		  SetRelativeOrder(coll, 1, q);
        		  SetRelativeOrder(coll, 2, q);
        		  SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
        		  SetConjugate(coll, 3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]);
        		  SetConjugate(coll, 4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]);
        		  G := PcpGroupByCollector(coll);
        	    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
           ## G2 semidirect product C_{q^2} \ltimes C_p^2
           G2 := function(p, q) #refined
              local mat, G, coll;
              mat := msg.QthRootGL2P(p, q);
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, q);
              SetRelativeOrder(coll, 2, q);
              SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
              SetPower(coll, 1, [2, 1]);
              SetConjugate(coll, 3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]);
              SetConjugate(coll, 4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]);
              G := PcpGroupByCollector(coll);
             return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
           end;
          return [G1(p, q), G2(p, q)];
          end;

    if (p + 1) mod q = 0 and q mod 2 = 1 then
      Append(s, case3(p, q));
		fi;
		if n = 36 then Append(s, case3(2, 3)); fi;

    #### case4: q^2 mid (p + 1)
    case4 := function(p, q) #refined
				  ## semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
				      local mat, matq, G, coll;
				      	mat := msg.QsquaredthRootGL2P(p, q);
								matq := mat^q;
				        coll := FromTheLeftCollector(4);
				        SetRelativeOrder(coll, 1, q);
								SetRelativeOrder(coll, 2, q);
								SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 1, [2, 1]);
								SetConjugate(coll, 3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]);
								SetConjugate(coll, 4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]);
								SetConjugate(coll, 3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]);
								SetConjugate(coll, 4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]);
								G := PcpGroupByCollector(coll);
								return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
							 end;

    if (p + 1) mod (q^2) = 0 then
    	Add(s, case4(p, q));
		fi;

    #### case5: q^2 mid (p - 1)
    case5 := function(p, q) #unrefined
      local list, t, i, G1, G2, G3, G4;
        list := [];
          ##G1 semidirect product of $C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_{q^2}
          G1 := function(p, q)
            local a, b, coll, r, rr, qq, ii, qqq, iii, G;
            ## get primitive root mod p^2
            	a := ZmodnZObj(Int(Z(p)),p^2);
              if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;
              r := Int(b^(p*(p-1)/(q^2)));
							rr := Int(b^(p*(p - 1)/q));
							ii := r mod p;
							qq := (r-ii)/p;
							iii := rr mod p;
							qqq := (rr-iii)/p;
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, q);
							SetRelativeOrder(coll, 2, q);
							SetPower(coll, 1, [2, 1]);
							SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
							SetPower(coll, 3, [4, 1]);
							SetConjugate(coll, 3, 1, [3, ii, 4, qq]);
							SetConjugate(coll, 4, 1, [4, ii]);
              SetConjugate(coll, 3, 2, [3, iii, 4, qqq]);
							SetConjugate(coll, 4, 2, [4, iii]);
              G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
          ##
          Add(list, G1(p, q));
          ##G2 semidirect product of $C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
          G2 := function(p, q)
            local a, b, coll, r, rr, G;
              a := Z(p);
              r := Int(a^((p-1)/(q^2)));
							rr := Int(a^((p-1)/q));
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, q);
							SetRelativeOrder(coll, 2, q);
              SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
							SetPower(coll, 1, [2, 1]);
              SetConjugate(coll, 3, 1, [3, r]);
							SetConjugate(coll, 3, 2, [3, rr]);
              G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
          ##
          Add(list, G2(p, q));
          ##G3 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
          G3 := function(i, p, q)
            local coll, a, b, c, r, rr, j, jj, k, G;
              c := Z(p);
              r := Int(c^((p-1)/(q^2)));
							rr := Int(c^((p-1)/q));

              ## get primitive root mod q^2 for powers
              a := ZmodnZObj(Int(Z(q)),q^2);
                if not a^(q-1) = ZmodnZObj(1,q^2) then b := a; else b := a+1; fi;
              k := Int(b^i);

							j := Int((c^((p-1)/(q^2)))^k);
							jj := Int((c^((p-1)/q))^k);

              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, q);
							SetRelativeOrder(coll, 2, q);
              SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
							SetPower(coll, 1, [2, 1]);
              SetConjugate(coll, 3, 1, [3, r]);
              SetConjugate(coll, 4, 1, [4, j]);
							SetConjugate(coll, 3, 2, [3, rr]);
              SetConjugate(coll, 4, 2, [4, jj]);
              G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
          ##
          t := (q^2-q)/2;

          for i in [0..t] do Add(list, G3(i, p, q)); od;

          ##
          G4 := function(i, p, q)
            local coll, a, b, c, r, rr, j, jj, k, G;
              c := Z(p);
              r := c^((p-1)/(q^2));
              j := Int(r^(i*q));
              coll := FromTheLeftCollector(4);
              SetRelativeOrder(coll, 1, q);
							SetRelativeOrder(coll, 2, q);
              SetRelativeOrder(coll, 3, p);
              SetRelativeOrder(coll, 4, p);
							SetPower(coll, 1, [2, 1]);
              SetConjugate(coll, 3, 1, [3, Int(r)]);
							SetConjugate(coll, 3, 2, [3, Int(r^q)]);
              SetConjugate(coll, 4, 1, [4, j]);
              G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;
          ##
          t := (q - 1);

          for i in [1..t] do Add(list, G4(i, p, q)); od;

          ##
          return list;
          end;
    if (p - 1) mod (q^2) = 0 and q mod 2 = 1 then
      Append(s, case5(p, q));
		fi;

    ####case6 q = 2
        case6 := function(p)
          local ll, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13;
            ll := [];

            ## semidirect product C_4 \ltimes C_{p^2}, \phi(Q) = C_2
            g1 := function(p) #unrefined
              local coll, G;
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
								SetPower(coll, 1, [2, 1]);
                SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 3, [4, 1]);
                SetConjugate(coll, 3, 1, [3, p-1, 4, p-1]);
								SetConjugate(coll, 4, 1, [4, p-1]);
                G := PcpGroupByCollector(coll);
                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
            Add(ll, g1(p));

						## semidirect product C_4 \ltimes C_p^2 \phi(Q) = C_2
						g2 := function(p)
							local coll, G;
								coll := FromTheLeftCollector(4);
								SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
								SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 1, [2, 1]);
								SetConjugate(coll, 3, 1, [3, p-1]);
								G := PcpGroupByCollector(coll);
							return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
						end;

						g3 := function(p)
							local coll, G;
								coll := FromTheLeftCollector(4);
								SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
								SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 1, [2, 1]);
								SetConjugate(coll, 3, 1, [3, p-1]);
								SetConjugate(coll, 4, 1, [4, p-1]);
								G := PcpGroupByCollector(coll);
							return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
						end;

						Add(ll, g2(p));
						Add(ll, g3(p));

						# semidirect product C_2^2 \ltimes C_{p^2}, \phi(Q) = C_2
						g4 := function(p) #unrefined
							local coll, G;
						  	coll := FromTheLeftCollector(4);
								SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
								SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 3, [4, 1]);
								SetConjugate(coll, 3, 1, [3, p-1, 4, p-1]);
								SetConjugate(coll, 4, 1, [4, p-1]);
								G := PcpGroupByCollector(coll);
							return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
						end;

						Add(ll, g4(p));

            ## semidirect product C_2^2 \ltimes C_p^2, \phi(Q) = C_2
            g5 := function(p)
              local coll, G;
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetConjugate(coll, 3, 1, [3, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            g6 := function(p)
              local coll, G;
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetConjugate(coll, 3, 1, [3, p-1]);
                SetConjugate(coll, 4, 1, [4, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            ## semidirect product C_2^2 \ltimes C_p^2 \phi(Q) = C_2^2
            g7 := function(p)
              local coll, G;
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetConjugate(coll, 3, 1, [3, p-1]);
                SetConjugate(coll, 4, 2, [4, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            Add(ll, g5(p));
            Add(ll, g6(p));
            Add(ll, g7(p));

						## semidirect product C_4 \ltimes C_{p^2}, \phi(Q) = C_4
            g8 := function(p) #unrefined
              local coll, G, a, b, r, rr, qq, ii;

                ## find primitive root modulo p^2
                a := ZmodnZObj(Int(Z(p)),p^2);
                if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1; fi;

                r := Int(a^((p^2-p)/4));
								ii := r mod p;
								qq := (r-ii)/p;

                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
								SetPower(coll, 1, [2, 1]);
                SetRelativeOrder(coll, 3, p);
								SetRelativeOrder(coll, 4, p);
								SetPower(coll, 3, [4, 1]);
                SetConjugate(coll, 3, 1, [3, ii, 4, qq]);
								SetConjugate(coll, 4, 1, [4, ii]);
								SetConjugate(coll, 3, 2, [3, p-1, 4, p-1]);
								SetConjugate(coll, 4, 2, [4, p-1]);
                G := PcpGroupByCollector(coll);
                return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
            if p mod 4 = 1 then
            Add(ll, g8(p)); fi;

            ## semidirect product C_4 \ltimes C_p^2 \phi(Q) = C_4
            g9 := function(p)
              local coll, G, a, r;
                a := Z(p);
                r := Int(a^((p - 1)/4));

                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetPower(coll, 1, [2, 1]);
                SetConjugate(coll, 3, 1, [3, r]);
                SetConjugate(coll, 3, 2, [3, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            g10 := function(p)
              local coll, G, a, r;
                a := Z(p);
                r := Int(a^((p - 1)/4));
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetPower(coll, 1, [2, 1]);
                SetConjugate(coll, 3, 1, [3, r]);
                SetConjugate(coll, 3, 2, [3, p-1]);
                SetConjugate(coll, 4, 1, [4, r]);
                SetConjugate(coll, 4, 2, [4, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

						g11 := function(p)
              local coll, G, a, r, k;
                a := Z(p);
                r := Int(a^((p - 1)/4));
                k := Int((a^((p - 1)/4))^3);
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetPower(coll, 1, [2, 1]);
                SetConjugate(coll, 3, 1, [3, r]);
                SetConjugate(coll, 3, 2, [3, p-1]);
                SetConjugate(coll, 4, 1, [4, k]);
                SetConjugate(coll, 4, 2, [4, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            g12 := function(p)
              local coll, G, a, r;
                a := Z(p);
                r := Int(a^((p - 1)/4));
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
                SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
                SetPower(coll, 1, [2, 1]);
                SetConjugate(coll, 3, 1, [3, p-1]);
                SetConjugate(coll, 4, 1, [4, r]);
                SetConjugate(coll, 4, 2, [4, p-1]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            if p mod 4 = 1 then
             Append(ll, [g9(p), g10(p), g11(p), g12(p)]);
						fi;

            g13 := function(p)
              local coll, G, mat, mat2;
                mat := msg.QsquaredthRootGL2P(p, 2);
								mat2 := mat^2;
                coll := FromTheLeftCollector(4);
                SetRelativeOrder(coll, 1, 2);
								SetRelativeOrder(coll, 2, 2);
                SetRelativeOrder(coll, 3, p);
                SetRelativeOrder(coll, 4, p);
								SetPower(coll, 1, [2, 1]);
                SetConjugate(coll, 3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]);
                SetConjugate(coll, 4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]);
								SetConjugate(coll, 3, 2, [3, Int(mat2[1][1]), 4, Int(mat2[2][1])]);
								SetConjugate(coll, 4, 2, [3, Int(mat2[1][2]), 4, Int(mat2[2][2])]);
                G := PcpGroupByCollector(coll);
              return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            end;

            if p mod 4 = 3 then
            Add(ll, g13(p)); fi;

            return ll;
          end;
    if q = 2 and p > 3 then
			Append(s, case6(p)); fi;
    return s;
  end );
        ##
############################################################################
	deltaDivisibility := function(x, y)
	  local w;
	    if x mod y = 0 then w := 1;
	    else w := 0; fi;
	  return w;
	  end;
############################################################################
	NumberGroupsP2Q2 := function(n)
		local fac, p, q, w;
				fac := Factors(n);
				## check input
				if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
					Error("Argument has to be of the form p^2*q^2, where p, q are primes");
				fi;

				q := fac[1];
				p := fac[4];
				if n = 36 then w := 14;
				elif q = 2 then w := 11 + 5*deltaDivisibility((p-1), 4) + deltaDivisibility((p+1), 4);
				else w := 4 + (6+q)*deltaDivisibility((p-1), q) + (4+q+q^2)*deltaDivisibility((p-1), q^2)/2 + 2*deltaDivisibility((p+1),q) + deltaDivisibility((p+1), q^2);
				fi;
			return w;
		end;
############################################################################
	IsP2Q2 := function(n)
	 local fac;
	       fac := Factors(n);
	 if not Length(fac)= 4 or not Length(Collected(fac)) = 2 or not fac[1] = fac[2] or not fac[3] = fac[4] then
	 		 return false;
	 else return true;
	 fi;
	 end;
