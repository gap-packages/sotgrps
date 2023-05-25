## Some test functions

LoadPackage("sotgrps");

###
###
## The following are test functions.
#
#
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

## minimal sanity check for large orders
SOTRec.testSOTconst := function(n)
	local all, g, id;
		all := AllSOTGroups(n);
		g := all[Random([1..NumberOfSOTGroups(n)])];
		id := IdSOTGroup(g);
		if not IsIsomorphicSOTGroups(g, SOTGroup(id[1],id[2])) then Error("Revise p4q.");fi;
	end;

## SOTRec.testIdSOTGroup(n) tests whether the same isomorphism type (given as random isomorphic copies of permutation groups) has the same SOT-group ID.
## test against SOT itself
SOTRec.testIdSOTGroup := function(orders)
	local n, nr, gap, sot, soty, i, copies,  gapid, new;
	if IsInt(orders) then orders := [orders]; fi;
	for n in orders do
	   if IsSOTAvailable(n) then
	      nr  := NumberOfSOTGroups(n);
	      gap := SmallGroupsAvailable(n) and IdGroupsAvailable(n);
	      Print("order ", n, ": testing ", nr, " groups\n");

	      sot := List([1..nr],x->SOTGroup(n,x));
	      soty := AllSOTGroups(n);
	      for i in [1..nr] do
	          copies := [];
			  if n < 5000 then
				  Add(copies, getRandomPerm(sot[i]));
				  Add(copies, getRandomPerm(soty[i]));
				  if IsSolvableGroup(sot[i]) then
					  Add(copies, getRandomPc(copies[2]));
				  fi;
			  else Append(copies, [getRandomPc(sot[i]), getRandomPc(soty[i])]);
			  fi;

		  if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then Error("Revise SOT ID", [n,i]); fi;
	      od;

	    ## can compare with gap library?
	      if gap then
	      gapid := List(sot,IdSmallGroup);
		  if not Size(gapid) = NumberSmallGroups(n) then Error("Revise enumeration."); fi;
		  if not IsDuplicateFreeList(gapid) then Error("Revise ID and construction."); fi;
	      new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
		  if not IsDuplicateFreeList(new) then Error("Revise SOT ID."); fi;
	      fi;

	   fi;
	od;;
	end;
