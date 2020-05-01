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
	local fac, p, q, AbelianGroupsP2Q, NonabelianGroupP2Qcase1, NonabelianGroupsP2Qcase2,
         NonabelianGroupsP2Qcase3, NonabelianGroupsOrderTwelve, NonabelianGroupsP2Qcase4, s;
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
    s := [];
    AbelianGroupsP2Q := function(p, q)
      local data1, data2, list;
        data1 := [ [p, p, q], [1, [2, 1]], [2, [3, 1]] ];
        data2 := [ [p, p, q], [2, [3, 1]] ];
        list := [ msg.groupFromData(data1), msg.groupFromData(data2) ];
      return list;
    end;
    Append(s, AbelianGroupsP2Q(p, q));
##case 1: p > q and q > 2 and q divides p + 1
####
  	NonabelianGroupP2Qcase1 := function(p, q) ##C_q \ltimes C_p^2, Q is irreducible in GL(2, p)
      local data1, G;
      if p > q and q > 2 and (p + 1) mod q = 0 then
        data1 := [ [q, p, p], [2, 1, [2, Int(msg.QthRootGL2P(p, q)[1][1]), 3, Int(msg.QthRootGL2P(p, q)[2][1])]], [3, 1, [2, Int(msg.QthRootGL2P(p, q)[1][2]), 3, Int(msg.QthRootGL2P(p, q)[2][2])]] ];
        G := msg.groupFromData(data1);
      fi;
        return G;
      end;
####
    if p > q and q > 2 and (p + 1) mod q = 0 then
     Add(s, NonabelianGroupP2Qcase1(p, q));
    fi;
####
  	NonabelianGroupsP2Qcase2 := function(p, q) ##case 2: p > q and q > 2 and q divides p - 1
  		local data1, data2_k, data3, k, list;
        list := [];
        ##
        if (p - 1) mod q = 0 then
          data1 := [ [q, p, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ]; ##(C_q \ltimes C_p) times C_p
          Add(s, msg.groupFromData(data1));
          data2_k := function(i) ##C_q \ltimes C_p^2
              local data, a, b, c, G;
                a:= (Z(p))^((p-1)/q);
                b:= Int((Z(q))^i);
                c:= a^b;
                data := [ [q, p, p], [2, 1, [2, Int(a)]], [3, 1, [3, Int(c)]] ];
              return data;
          end;
          ##
          for k in [0..(q - 1)/2] do Add(list, msg.groupFromData(data2_k(k))); od;
                #Info(InfoMSG,2,"start NonabelianGroupsP2Qcase2");
          ##
          data3 := function(p, q) ##C_q \ltimes C_{p^2}
            local data, a, b, c, qq, ii;
              a := ZmodnZObj(Int(Z(p)),p^2);
              if not a^(p-1) = ZmodnZObj(1,p^2) then b := a; else b := a+1;
              fi;
              c := Int(b^(p*(p-1)/q));
              ii := c mod p;
              qq := (c - ii)/p;
              data := [ [q, p, p], [2, [3, 1]], [2, 1, [2, ii, 3, qq]], [3, 1, [3, ii]] ];
            return data;
          end;
          Add(s, msg.groupFromData(data3(p, q)));
        fi;
        return list;
      end;
####
    if p > q and q > 2 and (p - 1) mod q = 0 then
      Append(s, NonabelianGroupsP2Qcase2(p, q));
    fi;
####
    NonabelianGroupsP2Qcase3 := function(p, q) ##case 3: p > q and q = 2
      local data1, data2, data3, list;
        data3 := [ [2, p, p], [2, 1, [2, p - 1]], [3, 1, [3, p - 1]] ]; ##C_2 \ltimes C_p^2
        data2 := [ [2, p, p], [2, 1, [2, p - 1]] ]; ##D_p \times C_p
        data1 := [ [2, p, p], [2, [3, 1]], [2, 1, [2, p - 1, 3, p - 1]], [3, 1, [3, p - 1]] ]; ##D_{p^2}
        list  := [ msg.groupFromData(data1), msg.groupFromData(data2), msg.groupFromData(data3) ];
      return list;
    end;
####
    if p > q and q = 2 then
      Append(s, NonabelianGroupsP2Qcase3(p, q));
    fi;
####
    NonabelianGroupsOrderTwelve := function()       ##order 12
      local data1, data2, data3, list;
        data1 := [ [3, 2, 2], [2, 1, [3, 1]], [3, 1, [2, 1, 3, 1]] ];
        data2 := [ [2, 2, 3], [2, [3, 1]], [2, 1, [2, 1, 3, 2]], [3, 1, [3, 2]] ];
        data3 := [ [2, 2, 3], [1, [2, 1]], [3, 1, [3, 2]] ];
        list := [ msg.groupFromData(data1), msg.groupFromData(data2), msg.groupFromData(data3) ];
        return list;
      end;
####
    if p = 2 and q = 3 then
      Append(s, NonabelianGroupsOrderTwelve());
    fi;
####
    NonabelianGroupsP2Qcase4 := function(p, q) ## case4: q > p and q > 3
      local data1, data2, data3, list, a;
        a := Z(q);
        if (q - 1) mod p = 0 and q > 3 then
          data1 := [ [p, p, q], [3, 1, [3, Int(a^((q - 1)/p))]] ]; ##C_p \times (C_p \ltimes C_q)
          data2 := [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(a^((q - 1)/p))]] ]; ## C_{p^2} \ltimes C_q
        fi;
        if (q - 1) mod (p^2) = 0 and q > 2 then
          data3 := [ [p, p, q], [1, [2, 1]], [3, 1, [3, Int(a^((q - 1)/(p^2)))]], [3, 2, [3, Int(a^((q - 1)/p))]]]; ## C_{p^2} \ltimes C_q
        fi;

        list := [];
        if (q - 1) mod p = 0 and q > 3 then
          Append(list, [msg.groupFromData(data1), msg.groupFromData(data2)]);
        fi;
        if (q - 1) mod (p^2) = 0 and q > 2 then
          Add(list, msg.groupFromData(data3));
        fi;
      return list;
    end;
####
    if q > p and q > 3 then
      Append(s, NonabelianGroupsP2Qcase4(p, q));
    fi;
##now add all groups in by case distinction
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
