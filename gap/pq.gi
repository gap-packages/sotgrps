#Classification of groups of order pq
####The following functions contribute to AllSOTGroups, NumberOfSOTGroups, and SOTGroup, respectively.
##############################################
SOTRec.allGroupsPQ := function(p, q)
local abelian, nonabelian, s;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    ## typ pq
    abelian := [ [p, q] ];
    if not (p - 1) mod q = 0 then
      s := [SOTRec.groupFromData(abelian)];
      return s;
    else
      ## typ Dpq
      nonabelian := [ [q, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ];
      s := [SOTRec.groupFromData(nonabelian),SOTRec.groupFromData(abelian)];
    fi;
  return s;
end;

##############################################
SOTRec.NumberGroupsPQ := function(p, q)
local w;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    w := 1 + SOTRec.w((p - 1), q);
  return w;
end;
##############################################
SOTRec.GroupPQ := function(p, q, i)
local all, G;
    ####
    Assert(1, p > q);
    Assert(1, IsPrimeInt(p));
    Assert(1, IsPrimeInt(q));
    ####
    all := [ [ [p, q] ] ];
    if (p - 1) mod q = 0 then
      Add(all, [ [q, p], [2, 1, [2, Int((Z(p))^((p-1)/q))]] ], 1);
    fi;

    if i < 2 + SOTRec.w((p - 1), q) then
      G := SOTRec.groupFromData(all[i]);
    fi;
  return G;
end;
