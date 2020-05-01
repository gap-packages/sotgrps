USE_NC := true;
USE_PCP := false;
##############################
groupFromData := function(data)
  local coll, i, j, n ,G;
   n := Size(data[1]);
   coll := FromTheLeftCollector(n);
   for i in [1..n] do SetRelativeOrder(coll,i,data[1][i]); od;
   for i in [2..Length(data)] do
      if IsInt(data[i][2]) then
         SetConjugateNC(coll,data[i][1],data[i][2],data[i][3]);
      else
         SetPowerNC(coll,data[i][1],data[i][2]);
      fi;
   od;
   UpdatePolycyclicCollector(coll);
  if USE_NC then
    G := PcpGroupByCollectorNC(coll);
  else G := PcpGroupByCollector(coll);
  fi;
  if USE_PCP = false then
    return PcpGroupToPcGroup(G:FreeGroupFamilyType:="syllable");
  else return G;
  fi;
end;
##############################
