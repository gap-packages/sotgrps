## Some test functions

LoadPackage("sotgrps");
LoadPackage("grpconst");

###
###
## The following are test functions.
#
# SOTRec.testAllSOTGroups compares AllSOTGroups with AllSmallGroups, if possible
SOTRec.testAllSOTGroups := function(n)
	local sotgroups, lib, duplicates, missing;
				duplicates := [];
				missing    := [];
				sotgroups   := List(AllSOTGroups(n),x->IdSmallGroup(x)[2]);
						lib    := [1..NumberSmallGroups(n)];
				if Size(sotgroups) = NumberSmallGroups(n) and AsSet(sotgroups) = lib then
					return true;
				elif not Size(sotgroups) = NumberSmallGroups(n) or not AsSet(sotgroups) = lib then
					Append(duplicates, List(Filtered(Collected(sotgroups), x->x[2] > 1), x->x[1]));
					Print(("duplicate groups of order "), n,(" with id "), duplicates, ", ");
					 Append(missing, Filtered(lib, x-> not x in sotgroups));
					Print(("missing groups of order "), n,(" with id "), missing, ".");
				fi;
end;

## SOTRec.testSOTGroup([a, b]) tests the functions for groups of order n such that a ≤ n ≤ b by comparing the size of the output of AllSOTGroups(n) and the enumeration NumberOfSOTGroups(n),
  ## and tests whether IdSOTGroup(SOTGroup(n, i)) = (n, i) and IdSOTGroup(AllSOTGroups(n)[i]) = (n, i).
  ## testAll() runs the above test for all nontrivial SOT groups of order available up to 10^6.
SOTRec.testSOTGroup := function(arg)
  local todo, nr, i, sotCnstAll, sotCnstbyID, sotID, sgl, ids, idss;
	  USE_NC:=false;
	  if Length(arg) = 2 then
	    todo := Filtered([arg[1]..arg[2]], x-> IsSOTAvailable(x));
	  elif Length(arg) = 0 then
			todo := Filtered([2..50000], x-> IsSOTAvailable(x));
		elif Length(arg) = 1 then
			todo := Filtered([2..arg], x-> IsSOTAvailable(x));
	  fi;
	  for i in todo do
	    nr := NumberOfSOTGroups(i);
	    Print("start ",nr," groups of size ",i,"\n");
	    sgl := SmallGroupsAvailable(i);
	    if sgl then
	      if NumberSmallGroups(i) <> nr then
	        Error("Revise NumberOfSOTGroups for order ",i,": there are ",NumberSmallGroups(i)," groups \n");
	      fi;
	    fi;

	    sotCnstbyID := List([1..nr],x->SOTGroup(i,x));
	    ids := List(sotCnstbyID, x->IdSOTGroup(x)[2]);
	    sotCnstAll := AllSOTGroups(i);
	    idss := List(sotCnstAll, x->IdSOTGroup(x)[2]);
	    if not ids = [1..nr] then
	      Error("Revise SOTGroup/IdSOTGroup for order ",i,": ids are",ids,"\n");
	    fi;
	    if not idss = [1..nr] then
	      Error("Revise AllSOTGroups/IdSOTGroup for order ",i,": ids are",idss,"\n");
	    fi;
	  od;
	  USE_NC := true;
	  return true;
end;



## SOTRec.testNumberOfSOTGroups([from, to]) compares enumeration given by NumberOfSOTGroups(n) and NumberSmallGroups(n) for n in [from..to].
SOTRec.testNumberOfSOTGroups := function(arg)
local todo, i, sot, gap;
	if Length(arg) = 2 then
   todo:=Filtered([arg[1]..arg[2]], x->IsSOTAvailable(x) and SmallGroupsAvailable(x));;
	 elif Length(arg) = 1 then
		 todo:=Filtered([2..arg[1]], x->IsSOTAvailable(x) and SmallGroupsAvailable(x));;
	 elif Length(arg) = 0 then
		 todo:=Filtered([2..10^6], x->IsSOTAvailable(x) and SmallGroupsAvailable(x));;
	 fi;
   for i in todo do
		 # Display(i);
		 sot:=NumberOfSOTGroups(i);
		 gap:=NumberSmallGroups(i);
      if not sot = gap then
         Error("ERROR at order ",i,"\n");
      fi;
   od;
   return true;
end;

## getRandomPerm(G) returns a permutation group that is a random isomorphism copy of G.
getRandomPerm := function(G)
	local H, gens, K;
	    H := Image(IsomorphismPermGroup(G));
	    repeat
	       gens := List([1..Size(GeneratorsOfGroup(G))+3],x->Random(H));
	       K := Group(gens);
	    until Size(K) = Size(G);
	    return K;
	end;

## getRandomPerm(G) returns a PcGroup that is a random isomorphism copy of G.
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


## SOTRec.testIdSOTGroup(n) tests whether the same isomorphism type (given as random isomorphic copies of permutation groups) has the same SOT-group ID.
## test against SOT itself
SOTRec.testIdSOTGroup := function(orders)
	local n, nr, gap, sot, soty, i, copies,  gapid, new;
	for n in orders do
	   if IsSOTAvailable(n) then
	      nr  := NumberOfSOTGroups(n);
	      gap := SmallGroupsAvailable(n);
	      Print("order ", n, ": testing ", nr, " groups\n");

	      sot := List([1..nr],x->SOTGroup(n,x));
	      soty := AllSOTGroups(n);
	      for i in [1..nr] do
	          copies := [];
	          Add(copies, getRandomPerm(sot[i]));
	          Add(copies, getRandomPerm(soty[i]));
	          if IsSolvableGroup(sot[i]) then
	              Add(copies, getRandomPc(copies[1]));
	              Add(copies, getRandomPc(copies[2]));
	          fi;

		  if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then Error("SOT ID perm", [n,i]); fi;
	      od;

	    ## can compare with gap library?
	      if gap then
	      gapid := List(sot,IdSmallGroup);
		  if not Size(gapid) = NumberSmallGroups(n) then Error("gap nr"); fi;
		  if not IsDuplicateFreeList(gapid) then Error("gap id"); fi;
	      new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
		  if not IsDuplicateFreeList(new) then Error("SOT id"); fi;
	      fi;

	   fi;
	od;;
	return true;
	end;

## SOTRec.testIdSOTGroupPc(n) tests whether the same isomorphism type (given as random isomorphic copies of PcGroups) has the same SOT-group ID.
SOTRec.testIdSOTGroupPc := function(orders)
	local n, nr, gap, sot, i, copies, gapid, new;
	for n in orders do
	   if IsSOTAvailable(n) then
	      nr  := NumberOfSOTGroups(n);
	      gap := SmallGroupsAvailable(n);
	      Print("start ",nr," groups of size ",n,"\n");

	      sot := List([1..nr],x->AllSOTGroups(n)[x]);
	      for i in [1..nr] do
	          copies := List([1..5],x->getRandomPc(sot[i]));
		  if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then Error("SOT ID pc", [n,i]); fi;
	      od;
	      Display(" ... SOT output correct");

	    ## can compare with gap library?
	      if gap then
	          gapid := List(sot,IdSmallGroup);
		  if not Size(gapid) = NumberSmallGroups(n) then Error("gap nr"); fi;
		  if not IsDuplicateFreeList(gapid) then Error("gap id"); fi;
	          new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
		  if not IsDuplicateFreeList(new) then Error("SOT id"); fi;
		  Display(" ... gap comparison ok");
	      fi;

	   fi;
	od;
	return true;
	end;

## test by RandomIsomorphismTest
SOTRec.testbyRandomIsomorphismTest := function(x)
local t,sot,gap,tg,cd;
   if not IsSOTAvailable(x) then Error("Wrong input."); fi;
   t := Runtime();
   sot := AllSOTGroups(x);
   t := Runtime()-t;
   Display(["done",x,Size(sot),t]);
   if SmallGroupsAvailable(x) then
      if not Size(sot)=NumberSmallGroups(x) then Error("Revise enumeration."); fi;
      if not AsSet(List(sot,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("Gulp! Construction contains duplicate(s)!");fi;
   else
      Print("start gap\n");
      tg := Runtime();
      gap := ConstructAllGroups(x);
      tg := Runtime()-tg;
      if not Size(sot)=Size(gap) then Error("Revise enumeration."); fi;
      Display([x,t,tg]);
      cd := List(sot,x->rec(order:=Size(x),code:=CodePcGroup(x)));
      Print("start random\n");
      cd := RandomIsomorphismTest(cd,10);
      if Size(cd)<Size(sot) then Error("random is"); else Print("ok\n");fi;
   fi;
   if not ForAll(sot,i->Order(i)=x) then Error("order"); fi;
   return t;
end;

## SOTConst returns runtime.
SOTconst := function( list )
	local nums, tm, tg, grg;

	   nums:= Sum(List(list,NumberOfSOTGroups));
	   Print("there are ",nums," groups \n");
	   tg  := Runtime();
	   grg := List(list,x->AllSOTGroups(x));
	   tg  := Runtime()-tg;
	   Print("SOT construction: ",tg,"\n");
	   tm  := Runtime();
	   return [nums,tg,tm];
	end;
