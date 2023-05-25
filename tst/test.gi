## Some test functions

LoadPackage("sotgrps");

###
###
## The following are test functions.
#
#
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
