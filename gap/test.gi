LoadPackage("sotgrps");
###
###

testAll := function()
  local nr, myCnstAll, myCnstbyID, myID, GAP;
  USE_NC := false;
  for i in Filtered([2..10^6], x-> SOTGroupIsAvailable(x)) do
    nr := NumberOfSOTGroups;
    Print("start ",nr," groups of size ",n,"\n");
    gap := SmallGroupsAvailable(i);
    if gap then
      if NumberSmallGroups(i) <> nr then
        Print("Revise NumberOfSOTGroups for order ",i,": there are ",NumberSmallGroups(i)," groups \n");
      fi;
    fi;

    myCnstbyID := List([1..nr],x->SOTGroup(n,x));
    myCnstAll := AllSOTGroups(n);
    if not List(myCnstbyID, x->IdSOTGroup(x)[2]) = [1..nr] then
      Print("Revise SOTGroup/IdSOTGroup for order ",i,": ids are",ids,"\n");
    fi;
    if not List(myCnstAll, x->IdSOTGroup(x)[2]) = [1..nr] then
      Print("Revise AllSOTGroups/IdSOTGroup for order ",i,": ids are",ids,"\n");
    fi;
  od;
  return true;
end;




msg.testAllEnumeration := function(from,to)
local todo, i, my, gap;
   todo:=Filtered([from..to], x->SOTGroupIsAvailable(x) and SmallGroupsAvailable(x));;
   for i in todo do Display(i); my:=NumberOfSOTGroups(i); gap:=NumberSmallGroups(i);
      if not my = gap then
         Error("ERROR at order ",i,"\n");
      fi;
   od;
   return true;
end;

getRandomPerm := function(G)
local H, gens, K;
    H := Image(IsomorphismPermGroup(G));
    repeat
       gens := List([1..Size(GeneratorsOfGroup(G))+3],x->Random(H));
       K := Group(gens);
    until Size(K) = Size(G);
    return K;
end;

getRandomPc := function(G)

local pcgs,H,ns,N,el,hom,Q,i,rel,els;
   if not IsPcGroup(G) then G := Image(IsomorphismPcGroup(G)); fi;
   els  := [];
   H    := G;
   rel  := [];
   repeat
      ns  := Filtered(MaximalSubgroupClassReps(H),x-> IsNormal(H,x) and
              Size(x)<Size(H) and IsPrimeInt(Size(H)/Size(x)));
      N   := Random(ns);
      hom := NaturalHomomorphismByNormalSubgroup(H,N);
      el  := MinimalGeneratingSet(Image(hom))[1];
      el  := el^Random(Filtered([1..Order(el)],i-> Gcd(i,Order(el))=1));
      if not Order(el) mod Size(Image(hom))=0 then Error("mhmm"); fi;
      Add(els,PreImagesRepresentative(hom,el));
      Add(rel,Size(Image(hom)));
      H   := N;
   until Size(H)=1;
   pcgs := PcgsByPcSequence(FamilyObj(els[1]),els);
   return GroupByPcgs(pcgs);
end;



testId := function(n)
local nr, gap, my, myy, i, copies,  gapid, new;

repeat
   n := n+1;
   if SOTGroupIsAvailable(n) then
      nr  := NumberOfSOTGroups(n);
      gap := SmallGroupsAvailable(n);
      Print("start ",nr," groups of size ",n,"\n");

      my := List([1..nr],x->SOTGroup(n,x));
      myy := AllSOTGroups(n);
      for i in [1..nr] do
          copies := [];
          Add(copies, getRandomPerm(my[i]));
          Add(copies, getRandomPerm(myy[i]));
          Add(copies, getRandomPc(copies[1]));
          Add(copies, getRandomPc(copies[2]));

	  if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then Error("my ID perm", [n,i]); fi;
      od;
      Display(" ... my stuff correct");

    ## can compare with gap library?
      if gap then
          gapid := List(my,IdSmallGroup);
	  if not Size(gapid) = NumberSmallGroups(n) then Error("gap nr"); fi;
	  if not IsDuplicateFreeList(gapid) then Error("gap id"); fi;
          new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
	  if not IsDuplicateFreeList(new) then Error("my id"); fi;
	  Display(" ... gap comparison ok");
      fi;

   fi;
until false;
return true;
end;

testIdPc := function(n)
local nr, gap, my, i, copies, gapid, new;

repeat
   n := n+1;
   if SOTGroupIsAvailable(n) then
      nr  := NumberOfSOTGroups(n);
      gap := SmallGroupsAvailable(n);
      Print("start ",nr," groups of size ",n,"\n");

      my := List([1..nr],x->AllSOTGroups(n)[x]);
      for i in [1..nr] do
          copies := List([1..5],x->getRandomPc(my[i]));
	  if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then Error("my ID pc", [n,i]); fi;
      od;
      Display(" ... my stuff correct");

    ## can compare with gap library?
      if gap then
          gapid := List(my,IdSmallGroup);
	  if not Size(gapid) = NumberSmallGroups(n) then Error("gap nr"); fi;
	  if not IsDuplicateFreeList(gapid) then Error("gap id"); fi;
          new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
	  if not IsDuplicateFreeList(new) then Error("my id"); fi;
	  Display(" ... gap comparison ok");
      fi;

   fi;
until false;
return true;
end;

SOTconst := function( list )
local nums, grps, ids, tm, tg, tim, tgi, ids2, grg, grm, tgm;

   nums:= Sum(List(list,NumberOfSOTGroups));
   Print("there are ",nums," groups \n");
   tg  := Runtime();
   grg := List(list,x->AllSOTGroups(x));
   tg  := Runtime()-tg;
   Print("SOT construction: ",tg,"\n");
   tm  := Runtime();
   return [nums,tg,tm];
end;
