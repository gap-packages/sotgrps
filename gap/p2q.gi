
MY_TEST_ALL := true;



Info(InfoMSG,2,"this is a test");
SetInfoLevel(InfoMSG,2);


if not MY_TEST_ALL then
   Print("INFO: code does NOT check consistency of groups\n");
fi;




##############################################################
msg.QthRootGL2P := function(p, q)
	local a, b;
	if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) or not (p^2-1) mod q = 0 then
	 Error("Arguments has to be primes p, q, where q divides (p^2 - 1).\n");
	 else
	 a := PrimitiveElement(GF(p^2));
	 b := a^((p^2-1)/q);
	fi;
   return [ [0, 1], [-b^(p+1), b+b^p] ] * One(GF(p));
 end;
##############################################################

InstallGlobalFunction( allGroupsP2Q, function(n)
	local fac, p, q, NonabelianGroupP2Qcase1, NonabelianGroupsP2Qcase2,
         NonabelianGroupsP2Qcase3, NonabelianGroupsOrderTwelve, NonabelianGroupsP2Qcase4, s, grp;
####
  fac := Factors(n);
  if not Length(fac) = 3 or fac[1] = fac[3] then
    Error("Argument has to be of the form p^2*q, where p, q are primes"); fi;
    p := fac[2];
    if fac[2] = fac[1] then
    q := fac[3];
    else
    q := fac[1];
    fi;

##case 1: p > q and q > 2 and q divides p + 1
####
	NonabelianGroupP2Qcase1 := function(p, q)
		  local mat, G, coll;
		    mat := msg.QthRootGL2P(p, q);
		    coll := FromTheLeftCollector(3);
		    SetRelativeOrder(coll, 1, q);
		    SetRelativeOrder(coll, 2, p);
		    SetRelativeOrder(coll, 3, p);
		    SetConjugate(coll, 2, 1, [2, Int(mat[1][1]), 3, Int(mat[2][1])]);
	      SetConjugate(coll, 3, 1, [2, Int(mat[1][2]), 3, Int(mat[2][2])]);
		    G := PcpGroupByCollector(coll);
	    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
	   end;
####

##case 2: p > q and q > 2 and q divides p - 1
####
	NonabelianGroupsP2Qcase2 := function(p, q)
		local GroupsP2QTypei, GroupP2QTypeii, GroupP2QTypeiii, i, t, r, list;

            #Info(InfoMSG,2,"start NonabelianGroupsP2Qcase2");

		     GroupsP2QTypei := function(i, p, q)
			       local coll, r, a, l, j, k, G;
			         r:= Z(p);
			         a:= Int(r^((p-1)/q));
               l:= Z(q);
			         k:= Int(l^i);
			         j:= Int((r^((p-1)/q))^k);
			         coll := FromTheLeftCollector(3);
			         SetRelativeOrder(coll, 1, q);
			         SetRelativeOrder(coll, 2, p);
			         SetRelativeOrder(coll, 3, p);
			         SetConjugate(coll, 2, 1, [2, a]);
			         SetConjugate(coll, 3, 1, [3, j]);
			         G := PcpGroupByCollector(coll);
		        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		       end;
		     GroupP2QTypeii := function(p, q)
			       local coll, r, a, G;
			         r := Z(p);
			         a := Int(r^((p-1)/q));
			         coll := FromTheLeftCollector(3);
			         SetRelativeOrder(coll, 1, q);
			         SetRelativeOrder(coll, 2, p);
			         SetRelativeOrder(coll, 3, p);
			         SetConjugate(coll, 2, 1, [2, a]);
			         G := PcpGroupByCollector(coll);
		        return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		       end;


        	GroupP2QTypeiii := function(p, q)
            ## semidirect product of C_{p^2} by C_q, but constructed by a refiend pcp-presentation
			     local coll, b, r, a, G, t, qq, ii;
		      ## get primitive root mod p^2
		           b := ZmodnZObj(Int(Z(p)),p^2);
			         if not b^(p-1) = ZmodnZObj(1,p^2) then r := b; else r := b+1; fi;

                        #t := Runtime();
               a := Int(b^(p*(p-1)/q));
 		        #Print("runtime new ",Runtime()-t,"\n");

			         coll := FromTheLeftCollector(3);
			         SetRelativeOrder(coll, 1, q);
			         SetRelativeOrder(coll, 2, p);
               SetRelativeOrder(coll, 3, p);
			         SetPower(coll,2,[3,1]);
                      ## write g_2^{g_1} = g_2^a as g_2^{ii}g_3^{qq} where a = qq*p+ii (div with remainder)
                        ii := a mod p;
			                  qq := (a - ii)/p;
			         SetConjugate(coll, 2, 1, [2, ii, 3, qq]);
			         SetConjugate(coll, 3, 1, [3, ii]);

                        if MY_TEST_ALL then
    			     G := PcpGroupByCollector(coll);
			                  else
                            G := PcpGroupByCollectorNC(coll);
                        fi;
            return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
		      end;



##
        t := (q-1)/2;
        list := [];
        Add(list, GroupP2QTypeii(p, q));
        for i in [0..t] do Add(list, GroupsP2QTypei(i, p, q)); od;
        Add(list, GroupP2QTypeiii(p, q));
    		return list;
    	end;

####
##case 3: p > q and q = 2
      	NonabelianGroupsP2Qcase3 := function(p, q)
                     local G1, G2, G3, list;
                     list := [];
                     G1 := function(p, q)
                             local coll, G;
                             coll := FromTheLeftCollector(3);
                             SetRelativeOrder(coll, 1, 2);
                             SetRelativeOrder(coll, 2, p);
                             SetRelativeOrder(coll, 3, p);
                             SetConjugate(coll, 2, 1, [2, p-1]);
                             SetConjugate(coll, 3, 1, [3, p-1]);
                             G := PcpGroupByCollector(coll);
                     return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                     end;
       ##
                     G2 := function(p, q)
                             local coll, G;
                             coll := FromTheLeftCollector(3);
                             SetRelativeOrder(coll, 1, 2);
                             SetRelativeOrder(coll, 2, p);
                             SetRelativeOrder(coll, 3, p);
                             SetConjugate(coll, 2, 1, [2, p-1]);
                             #SetConjugate(coll, 3, 1, [3, 1]);
                             G := PcpGroupByCollector(coll);
                     return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                     end;
       ##
                     G3 := function(p, q)
                      ## semidirect product of C_{p^2} by C_2, but constructed by a refined pc-presentation
                             local coll, G;
                             coll := FromTheLeftCollector(3);
                             SetRelativeOrder(coll, 1, 2);
                             SetRelativeOrder(coll, 2, p);
                             SetRelativeOrder(coll, 3, p);
                             SetPower(coll, 2, [3, 1]);
                             SetConjugate(coll, 2, 1, [2, p-1, 3, p-1]);
                             SetConjugate(coll, 3, 1, [3, p-1]);
                             G := PcpGroupByCollector(coll);
                     return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
                     end;
             Add(list, G1(p, q));
             Add(list, G2(p, q));
             Add(list, G3(p, q));
             return list;
             end;

      ####
      ##order 12

      	 NonabelianGroupsOrderTwelve := function()
        	  local G1, G2, G3, ss;
          	 ss := [];
          	 G1 := function()
            	   local coll, G;
            	    coll := FromTheLeftCollector(3);
            	    SetRelativeOrder(coll, 1, 3);
            	    SetRelativeOrder(coll, 2, 2);
            	    SetRelativeOrder(coll, 3, 2);
            	    SetConjugate(coll, 2, 1, [3, 1]);
                  SetConjugate(coll, 3, 1, [2, 1, 3, 1]);
      	          G := PcpGroupByCollector(coll);
            	return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
            	end;
            Add(ss, G1());
          	G2 := function()
            	  local coll, G;
            	   coll := FromTheLeftCollector(2);
            	   SetRelativeOrder(coll, 1, 2);
            	   SetRelativeOrder(coll, 2, 6);
            	   SetConjugate(coll, 2, 1, [2, 5]);
                 G := PcpGroupByCollector(coll);
            	return PcpGroupToPcGroup(RefinedPcpGroup(G));
            	end;
          	Add(ss, G2());
          	G3 := function()
            	  local coll, G;
            	   coll := FromTheLeftCollector(2);
            	   SetRelativeOrder(coll, 1, 4);
            	   SetRelativeOrder(coll, 2, 3);
            	   SetConjugate(coll, 2, 1, [2, 2]);
      	         G := PcpGroupByCollector(coll);
            	return PcpGroupToPcGroup(RefinedPcpGroup(G));
            	end;
           Add(ss, G3());
           return ss;
         end;

      ## case4: q > p and q > 3
          NonabelianGroupsP2Qcase4 := function(p, q)
            local G1, G2, G3, ss;
              ss := [];
              G1 := function(p, q)
                local a, r, coll, G;
                  a := Z(q);
                  r := Int(a^((q-1)/p));
                  coll := FromTheLeftCollector(3);
                  SetRelativeOrder(coll, 1, p);
                  SetRelativeOrder(coll, 2, p);
                  SetRelativeOrder(coll, 3, q);
                  SetConjugate(coll, 3, 1, [3, r]);
                  G := PcpGroupByCollector(coll);
            	return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
             end;
            if (q - 1) mod p = 0 and q > 3 then
      	         Add(ss, G1(p, q));
              fi;
              G2 := function(p, q)
                ## semidirect product of $C_q by C_{p^2}, constructed by refined pc-presentation
                local a, r, coll, G;
                  a := Z(q);
                  r := Int(a^((q-1)/p));
                  coll := FromTheLeftCollector(3);
                  SetRelativeOrder(coll, 1, p);
                  SetRelativeOrder(coll, 2, p);
                  SetRelativeOrder(coll, 3, q);
                  SetPower(coll, 1, [2, 1]);
                  SetConjugate(coll, 3, 1, [3, r]);
                  G := PcpGroupByCollector(coll);
            	  return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
              if (q - 1) mod p = 0 and q > 3 then
        	 Add(ss, G2(p, q));
          fi;
              G3 := function(p, q)
                local coll, a, r, k, G;
                  a := Z(q);
                  r := Int(a^((q-1)/(p^2)));
                  k := Int(a^((q-1)/(p)));
                  coll := FromTheLeftCollector(3);
                  SetRelativeOrder(coll, 1, p);
                  SetRelativeOrder(coll, 2, p);
                  SetRelativeOrder(coll, 3, q);
                  SetPower(coll, 1, [2, 1]);
                  SetConjugate(coll, 3, 1, [3, r]);
                  SetConjugate(coll, 3, 2, [3, k]);
                  G := PcpGroupByCollector(coll);
            	  return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
              end;
              if (q - 1) mod (p^2) = 0 then
            Add(ss, G3(p, q)); fi;
              return ss;
          end;

##now add all groups in by case distinction
  if not Gcd(p,q)=1 or not ForAll([p,q],IsPrimeInt) then
	Error("wrong input");
	fi;
	s := [];
	Add(s, AbelianGroup([p^2*q]));
	Add(s, AbelianGroup([p, p*q]));
	if p > q and q > 2 and (p + 1) mod q = 0 then
	 Add(s, NonabelianGroupP2Qcase1(p, q));
	fi;
	if p > q and q > 2 and (p - 1) mod q = 0 then
		Append(s, NonabelianGroupsP2Qcase2(p, q));
	fi;
	if p > q and q = 2 then
		for grp in NonabelianGroupsP2Qcase3(p, q) do
			Add(s, grp); od;
	fi;
	if p = 2 and q = 3 then for grp in NonabelianGroupsOrderTwelve() do Add(s, grp); od;
	fi;
	if q > p and q > 3 then for grp in NonabelianGroupsP2Qcase4(p, q) do Add(s, grp); od;
	fi;
return s;
end );

######################################################
deltaDivisibility := function(x, y)
  local w;
    if x mod y = 0 then w := 1;
    else w := 0; fi;
  return w;
  end;
######################################################
NumberGroupsP2Q := function(n)
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
    elif p > q then w := 2 + deltaDivisibility((p+1), q) + (q+5)*deltaDivisibility((p-1), q)/2;
    else w := 2 + 2*deltaDivisibility((q-1), p) + deltaDivisibility((q-1), p^2);
    fi;
  return w;
end;
######################################################



testMyallGroupsP2Q := function(n)
local mystuff, lib, i, j;
  ## this SHOULD be the set 1,2,3,.., NumberSmallGroups(p^2*q)
  Display("start");
   mystuff := AsSet(List(allGroupsP2Q(n),x->IdSmallGroup(x)[2]));

   		if not mystuff = [1..NumberSmallGroups(n)] then
     	 Error("ARRGGG... shit... revise!");
  		 else
         Display("end");
      return true;
   fi;
end;





testAllPrimesPQ := function()
local p,q;
  for p in Primes do
    Print("start prime ",p,"\n");
    for q in Primes do
       if not p = q then testMyallGroupsP2Q(p^2*q); fi;
    od;
  od;
  return true;
end;

testAllPrimes2PQ := function()
local p,q;
  for p in Primes2 do
    Print("start prime ",p,"\n");
    for q in Primes do
       if not p = q then testMyallGroupsP2Q(p^2*q); fi;
    od;
  od;
  return true;
end;
