############################################################################ all groups P2Q2
msg.allGroupsP2Q2 := function(n)
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
		  local t, c, l, i, G1, G2, G3, G4, G5, G6, G7, list;
		    list := [];
				c := Z(p);
				l := Z(q);
				if not (p - 1) mod q = 0 then return list; else
  		    ##G1 semidirect product of C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
  		    G1 := function(p, q) #refined
  		    	local a, b, r, qq, ii, data;
  		    ## get primitive root mod p^2
  		      	a := ZmodnZObj(Int(Z(p)), p^2);
  		        if not a^(p - 1) = ZmodnZObj(1,p^2) then
  							b := a;
  						else b := a + 1; fi;
  		        r := Int(b^(p*(p-1)/q));
  						ii := r mod p;
  						qq := (r - ii)/p;
  						data := [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ];
  		      return msg.groupFromData(data);
  		    end;
  		    ##
  		    Add(list, G1(p, q));
  		    ##
  		    ##G2 semidirect product of C_q^2 \ltimes C_{p^2}, \phi(Q) = C_q
  		    G2 := function(p, q) #refined
  		    	local a, b, r, qq, ii, data;
  		       ## get primitive root mod p^2
  		      	a := ZmodnZObj(Int(Z(p)),p^2);
  		        if not a^(p-1) = ZmodnZObj(1, p^2) then
  							b := a;
  						else b := a + 1; fi;
  		        r := Int(b^(p*(p - 1)/q));
  						ii := r mod p;
  						qq := (r - ii)/p;
  						data := [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ];
  		      return msg.groupFromData(data);
  		    end;
  		    ##
  		    Add(list, G2(p, q));
  		    ##
  		    ##G3 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
  		    G3 := function(p, q) #refined
  		      local data;
              data := [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(c^((p-1)/q))]] ];
  		      return msg.groupFromData(data);
  		    end;
  		    ##
  		    Add(list, G3(p, q));
  		    ##
  		    ##G4 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
  		    G4 := function(i, p, q) #refined
            local j, k, data;
              k := Int(l^i);
  		        j := Int(c^(k*(p-1)/q));
  				    data := [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(c^((p-1)/q))]], [4, 1, [4, j]] ];
  		      return msg.groupFromData(data);
  		    end;
  		    ##
  			  if (p - 1) mod q = 0 and q mod 2 = 1 then
            t := (q - 1)/2;
  			  else t := 0;
  				fi;

  		    for i in [0..t] do Add(list, G4(i, p, q)); od;
  		    ##
  	      ##G5 direct product of C_{qp} and semidirect product: C_q \times (C_q \ltimes C_p) \times C_p, \phi(Q) = C_q
  		    G5 := function(p, q) #refined
            local data;
              data := [ [q, q, p, p], [3, 1, [3, Int(c^((p-1)/q))]] ];
            return msg.groupFromData(data);
  		    end;
  		    ##
  	      Add(list, G5(p, q));
          ##
  		    ##G6 direct products of C_q and semidirect product: C_q \times (C_q \ltimes C_p^2), \phi(Q) = C_q
  		    G6 := function(i, p, q) #refined
            local j, k, data;
              k:= Int(l^i);
              j:= Int((c^((p-1)/q))^k);
              data := [ [q, q, p, p], [3, 1, [3, Int(c^((p-1)/q))]], [4, 1, [4, j]] ];
            return msg.groupFromData(data);
  		    end;
  		    ##
          if (p - 1) mod q = 0 and q mod 2 = 1 then
            t := (q - 1)/2;
          else t := 0;
          fi;

          for i in [0..t] do Add(list, G6(i, p, q)); od;
          ##
          ##G7 semidirect product ((C_q \times C_q) \ltimes C_p) \times C_p, \phi(Q) = C_q^2
  		    G7 := function(p, q) #refined
            local data;
  					  data := [ [q, q, p, p], [3, 1, [3, Int(c^((p-1)/q))]], [4, 2, [4, Int(c^((p-1)/q))]] ];
  		      return msg.groupFromData(data);
  		    end;
          ##
          Add(list, G7(p, q));
          ##
        fi;
      return list;
		end;
		if (p - 1) mod q = 0 and q > 2 then
		  Append(s, case2(p, q));
		fi;
		##
		if p = 3 and q = 2 then
		  Append(s, case2(p, q));
		fi;
		####
    #### case3: q mid (p + 1), q^2 nmid (p^2 - 1), q neq 2
    case3 := function(p, q)
      local G1, G2;
        ##G1 direct product of C_q and semidirect product: C_q \times (C_q \ltimes C_p^2)
        G1 := function(p, q) #refined
          local mat, data;
	        		mat := msg.QthRootGL2P(p, q);
							data := [ [q, q, p, p],
							[3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
							[4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ];
        	return msg.groupFromData(data);
        end;
        ## G2 semidirect product C_{q^2} \ltimes C_p^2
        G2 := function(p, q) #refined
          local mat, data;
	          mat := msg.QthRootGL2P(p, q);
						data := [ [q, q, p, p], [1, [2, 1]],
						[3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
						[4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]] ];
          return msg.groupFromData(data);
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
			local mat, matq, data;
				mat := msg.QsquaredthRootGL2P(p, q);
				matq := mat^q;
				data := [ [q, q, p, p], [1, [2, 1]],
				[3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
				[4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]],
				[3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
				[4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ];
			return msg.groupFromData(data);
		end;
		###
    if (p + 1) mod (q^2) = 0 and q mod 2 = 1 then
    	Add(s, case4(p, q));
		fi;
		###
		if p = 3 and q = 2 then
    	Add(s, case4(p, q));
		fi;
    #### case5: q^2 mid (p - 1)
    case5 := function(p, q) #unrefined
      local list, i, G1, G2, G3, G4;
        list := [];
        ##G1 semidirect product of $C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_{q^2}
        G1 := function(p, q)
          local a, b, r, rr, qq, ii, qqq, iii, data;
          ## get primitive root mod p^2
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p - 1) = ZmodnZObj(1, p^2) then b := a; else b := a + 1; fi;
            r := Int(b^(p*(p-1)/(q^2)));
						rr := Int(b^(p*(p - 1)/q));
						ii := r mod p;
						qq := (r-ii)/p;
						iii := rr mod p;
						qqq := (rr-iii)/p;
						data := [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ];
          return msg.groupFromData(data);
        end;
        ##
        Add(list, G1(p, q));
        ##G2 semidirect product of $C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
        G2 := function(p, q)
          local a, b, r, rr, data;
            a := Z(p);
            r := Int(a^((p - 1)/(q^2)));
						rr := Int(a^((p - 1)/q));
						data := [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, r]], [3, 2, [3, rr]] ];
          return msg.groupFromData(data);
        end;
        ##
        Add(list, G2(p, q));
        ##G3 semidirect product C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
        G3 := function(i, p, q)
          local a, b, c, r, rr, j, jj, k, data;
            c := Z(p);
            r := Int(c^((p-1)/(q^2)));
						rr := Int(c^((p-1)/q));
            a := ZmodnZObj(Int(Z(q)),q^2);
						if not a^(q - 1) = ZmodnZObj(1,q^2) then b := a; else b := a + 1; fi;
            k := Int(b^i);
						j := Int((c^((p-1)/(q^2)))^k);
						jj := Int((c^((p-1)/q))^k);
						data := [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, r]], [4, 1, [4, j]], [3, 2, [3, rr]], [4, 2, [4, jj]] ];
          return msg.groupFromData(data);
        end;
        ##
        for i in [0..(q^2 - q)/2] do Add(list, G3(i, p, q)); od;
        ##
        G4 := function(k, p, q)
          local c, r, data;
            c := Z(p);
            r := c^((p-1)/(q^2));
						data := [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(r)]], [3, 2, [3, Int(r^q)]], [4, 1, [4, Int(r^(k*q))]] ];
          return msg.groupFromData(data);
        end;
        ##
        for i in [1..(q - 1)] do Add(list, G4(i, p, q)); od;
        ##
        return list;
    end;
    if (p - 1) mod (q^2) = 0 and q mod 2 = 1 then
      Append(s, case5(p, q));
		fi;

    ####case6 q = 2
    case6 := function(p)
      local list, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13;
        list := [];
        G1 := function(p) ## semidirect product C_4 \ltimes C_{p^2}, \phi(Q) = C_2
          local data;
            data := [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ];
          return msg.groupFromData(data);
        end;
        Add(list, G1(p));

				## semidirect product C_4 \ltimes C_p^2 \phi(Q) = C_2
				G2 := function(p)
					local data;
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, (p - 1)]] ];
					return msg.groupFromData(data);
				end;

				G3 := function(p)
					local data;
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, p-1]] ];
					return msg.groupFromData(data);
				end;

				Append(list, [G2(p), G3(p)]);

				## semidirect product C_2^2 \ltimes C_{p^2}, \phi(Q) = C_2
				G4 := function(p) #unrefined
					local data;
						 data := [ [2, 2, p, p], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ];
					return msg.groupFromData(data);
				end;

				Add(list, G4(p));

        ## semidirect product C_2^2 \ltimes C_p^2, \phi(Q) = C_2
        G5 := function(p)
          local data;
            data := [ [2, 2, p, p], [3, 1, [3, p - 1]] ];
          return msg.groupFromData(data);
        end;

        G6 := function(p)
          local data;
            data := [ [2, 2, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ];
          return msg.groupFromData(data);
        end;

				Append(list, [G5(p), G6(p)]);

        ## semidirect product C_2^2 \ltimes C_p^2 \phi(Q) = C_2^2
        G7 := function(p)
          local data;
            data := [ [2, 2, p, p], [3, 1, [3, p-1]], [4, 2, [4, p-1]] ];
          return msg.groupFromData(data);
        end;

        Add(list, G7(p));

				## semidirect product C_4 \ltimes C_{p^2}, \phi(Q) = C_4
        G8 := function(p)
          local data, a, b, r, rr, qq, ii;
            a := ZmodnZObj(Int(Z(p)),p^2);
            if not a^(p - 1) = ZmodnZObj(1, p^2) then b := a; else b := a + 1; fi;
            r := Int(a^((p^2-p)/4));
						ii := r mod p;
						qq := (r - ii)/p;
						data := [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, p-1, 4, p-1]], [4, 2, [4, p-1]] ];
            return msg.groupFromData(data);
        end;

        if p mod 4 = 1 then
          Add(list, G8(p)); fi;

        ## semidirect product C_4 \ltimes C_p^2 \phi(Q) = C_4
        G9 := function(p)
          local data;
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ];
          return msg.groupFromData(data);
        end;

        G10 := function(p)
          local data, a, r;
            a := Z(p);
            r := Int(a^((p - 1)/4));
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, r]], [3, 2, [3, p-1]], [4, 1, [4, r]], [4, 2, [4, p-1]] ];
          return msg.groupFromData(data);
        end;

				G11 := function(p)
          local data, a, r, k;
            a := Z(p);
            r := Int(a^((p - 1)/4));
            k := Int((a^((p - 1)/4))^3);
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, r]], [3, 2, [3, p-1]], [4, 1, [4, k]], [4, 2, [4, p-1]] ];
          return msg.groupFromData(data);
        end;

        G12 := function(p)
          local data, a, r;
            a := Z(p);
            r := Int(a^((p - 1)/4));
						data := [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, r]], [4, 2, [4, p-1]] ];
          return msg.groupFromData(data);
        end;

        if p mod 4 = 1 then
          Append(list, [G9(p), G10(p), G11(p), G12(p)]);
				fi;

        G13 := function(p)
          local data, mat, mat2;
            mat := msg.QsquaredthRootGL2P(p, 2);
						mat2 := mat^2;
						data := [ [2, 2, p, p], [1, [2, 1]],
						[3, 1, [3, Int(mat[1][1]), 4, Int(mat[2][1])]],
						[4, 1, [3, Int(mat[1][2]), 4, Int(mat[2][2])]],
						[3, 2, [3, Int(mat2[1][1]), 4, Int(mat2[2][1])]],
						[4, 2, [3, Int(mat2[1][2]), 4, Int(mat2[2][2])]] ];
          return msg.groupFromData(data);
        end;

        if p mod 4 = 3 then
          Add(list, G13(p)); fi;

      return list;
    end;
    if q = 2 and p > 3 then
			Append(s, case6(p)); fi;
    return s;
  end;
##
############################################################################
msg.NumberGroupsP2Q2 := function(n)
		local fac, p, q, w;
				fac := Factors(n);
				## check input
				if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
					Error("Argument has to be of the form p^2*q^2, where p, q are primes");
				fi;

				q := fac[1];
				p := fac[4];
				if n = 36 then w := 14;
				elif q = 2 then w := 11 + 5*msg.deltaDivisibility((p-1), 4) + msg.deltaDivisibility((p+1), 4);
				else w := 4 + (6+q)*msg.deltaDivisibility((p-1), q) + (4+q+q^2)*msg.deltaDivisibility((p-1), q^2)/2 + 2*msg.deltaDivisibility((p+1),q) + msg.deltaDivisibility((p+1), q^2);
				fi;
			return w;
		end;
############################################################################

msg.isp2q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2]) = [ 2, 2 ];

############################################################################ all groups P2Q2
msg.GroupP2Q2 := function(n, i)
  local fac, p, q, a, b, c, d, e, f, qq, ii, qqq, iii, all, G, k, t, matq, matq2, matp, matp2;
    fac := Factors(n);
    if not Length(fac) = 4 or not fac[1] = fac[2] or not fac[3] = fac[4] then
      Error("Argument has to be of the form p^2*q^2, where p, q are primes");
		fi;
    q := fac[1];
    p := fac[4];
    #### case1: q nmid (p-1), q nmid (p^2 -1), q > 2
    all := [ [ [p, p, q, q], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, q, q], [3, [4, 1]] ], [ [p, p, q, q], [1, [2, 1]] ], [ [p, p, q, q], [2, [3, 1]] ] ];

    a := Z(p);
    b := Z(q);

    c := ZmodnZObj(Int(Z(p)), p^2);
    if not c^(p - 1) = ZmodnZObj(1, p^2) then
      d := c;
    else d := c + 1;
    fi;

    e := ZmodnZObj(Int(Z(q)), q^2);
    if not e^(q - 1) = ZmodnZObj(1, q^2) then
      f := e;
    else f := e + 1;
    fi;

    #### case2: q mid (p - 1), q^2 nmid (p^2 - 1)
    if (p - 1) mod q = 0 and q > 2 or n = 36 then
      ii := Int(d^(p*(p-1)/q)) mod p;
      qq := (Int(d^(p*(p-1)/q)) - ii)/p;
      Append(all, [ [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ], ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_q
      [ [q, q, p, p], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]] ], ##C_q^2 \ltimes C_{p^2}, \phi(Q) = C_q
      [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]] ] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
      if q mod 2 = 1 then
        t := (q - 1)/2;
      else t := 0;
      fi;
      for k in [0..t] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(Int(b^k)*(p-1)/q))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_q
      od;
      Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]] ]); ##C_q \times (C_q \ltimes C_p) \times C_p, \phi(Q) = C_q
      for k in [0..t] do
        Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int((a^(Int(b^k)*(p-1)/q)))]] ]); ##C_q \times (C_q \ltimes C_p^2), \phi(Q) = C_q
      od;
      Add(all, [ [q, q, p, p], [3, 1, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int(a^((p-1)/q))]] ]); ##((C_q \times C_q) \ltimes C_p) \times C_p, \phi(Q) = C_q^2
    fi;

    #### case3: q mid (p + 1), q^2 nmid (p^2 - 1)
    if (p + 1) mod q = 0 and q mod 2 = 1 then
      matq := msg.QthRootGL2P(p, q);
      Append(all, [ [ [q, q, p, p],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ], ##C_q \times (C_q \ltimes C_p^2)
      [ [q, q, p, p], [1, [2, 1]],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] ]); ##C_{q^2} \ltimes C_p^2
    fi;
    if n = 36 then
      matq := msg.QthRootGL2P(2, 3);
      Append(all, [ [ [3, 3, 2, 2],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ], ##C_2 \times (C_2 \ltimes C_3^2)
      [ [3, 3, 2, 2], [1, [2, 1]],
      [3, 1, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
      [4, 1, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ] ]); ##C_4 \ltimes C_3^2
    fi;
    #### case4: q^2 mid (p + 1)
    if ( p + 1) mod (q^2) = 0 and q > 2 or n = 36 then
      matq2 := msg.QsquaredthRootGL2P(p, q);
      matq := matq2^q;
      Add(all, [ [q, q, p, p], [1, [2, 1]],
				[3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
				[4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
				[3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
				[4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
		fi;

    #### case5: q^2 mid (p - 1)
    if (p - 1) mod (q^2) = 0 and q > 2 then
      ii := Int(d^(p*(p-1)/(q^2))) mod p;
      qq := (Int(d^(p*(p-1)/(q^2))) - ii)/p;
      iii := Int(d^(p*(p - 1)/q)) mod p;
      qqq := (Int(d^(p*(p - 1)/q)) - iii)/p;
      Append(all, [ [ [q, q, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, iii, 4, qqq]], [4, 2, [4, iii]] ],  ##C_{q^2} \ltimes C_{p^2}, \phi(Q) = C_{q^2}
      [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/(q^2)))]], [3, 2, [3, Int(a^((p - 1)/q))]] ] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
      for k in [0..(q^2 - q)/2] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [4, 1, [4, Int((a^(Int(f^k)*(p-1)/(q^2))))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 2, [4, Int((a^(Int(f^k)*(p-1)/q)))]] ]); ##C_{q^2} \ltimes C_p^2, \phi(Q) = C_{q^2}
      od;
      for k in [1..(q - 1)] do
        Add(all, [ [q, q, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p-1)/(q^2)))]], [3, 2, [3, Int(a^((p-1)/q))]], [4, 1, [4, Int(a^(k*(p-1)/q))]] ]);
      od;
    fi;

    ####case6 q = 2 and p > 3
    if q = 2 and p > 3 then
      Append(all, [ [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ], ##C_4 \ltimes C_{p^2}, \phi(Q) = C_2
      [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, (p - 1)]] ], ##C_4 \ltimes C_p^2 \phi(Q) = C_2
      [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, p-1]] ],
      [ [2, 2, p, p], [3, [4, 1]], [3, 1, [3, p-1, 4, p-1]], [4, 1, [4, p-1]] ], ##C_2^2 \ltimes C_{p^2}, \phi(Q) = C_2
      [ [2, 2, p, p], [3, 1, [3, p - 1]] ], ##C_2^2 \ltimes C_p^2, \phi(Q) = C_2
      [ [2, 2, p, p], [3, 1, [3, p - 1]], [4, 1, [4, p - 1]] ],
      [ [2, 2, p, p], [3, 1, [3, p-1]], [4, 2, [4, p-1]] ] ]); ##C_2^2 \ltimes C_p^2 \phi(Q) = C_2^2
      if p mod 4 = 1 then
        ii := Int(d^((p^2-p)/4)) mod p;
        qq := (Int(d^((p^2-p)/4)) - ii)/p;
        Append(all, [ [ [2, 2, p, p], [1, [2, 1]], [3, [4, 1]], [3, 1, [3, ii, 4, qq]], [4, 1, [4, ii]], [3, 2, [3, p - 1, 4, p - 1]], [4, 2, [4, p - 1]] ],  ##C_4 \ltimes C_{p^2}, \phi(Q) = C_4
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int((Z(p))^((p - 1)/4))]], [3, 2, [3, p - 1]] ], ##C_4 \ltimes C_p^2 \phi(Q) = C_4
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ],
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, Int(a^((p - 1)/4))]], [3, 2, [3, p-1]], [4, 1, [4, Int(a^(3*(p - 1)/4))]], [4, 2, [4, p-1]] ],
        [ [2, 2, p, p], [1, [2, 1]], [3, 1, [3, p-1]], [4, 1, [4, Int(a^((p - 1)/4))]], [4, 2, [4, p-1]] ] ]);
      fi;
      if p mod 4 = 3 then
        matq2 := msg.QsquaredthRootGL2P(p, 2);
        matq := matq2^q;
        Add(all, [ [2, 2, p, p], [1, [2, 1]],
        [3, 1, [3, Int(matq2[1][1]), 4, Int(matq2[2][1])]],
        [4, 1, [3, Int(matq2[1][2]), 4, Int(matq2[2][2])]],
        [3, 2, [3, Int(matq[1][1]), 4, Int(matq[2][1])]],
        [4, 2, [3, Int(matq[1][2]), 4, Int(matq[2][2])]] ]);
      fi;
    fi;

    if i < (msg.NumberGroupsP2Q2(n) + 1) then
      G := msg.groupFromData(all[i]);
    fi;
  return G;
end;
