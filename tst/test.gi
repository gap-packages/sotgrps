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
       todo := [arg[1]..arg[2]];
   elif Length(arg) = 1 then
       todo := [2..arg[1]];
   elif Length(arg) = 0 then
       todo := [2..50000];
   fi;
   todo := Filtered(todo, x-> IsSOTAvailable(x) and SmallGroupsAvailable(x));
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
	    if Size(G) <= 100 then
	        H := Image(RegularActionHomomorphism(G));
	    else
	        H := Image(IsomorphismPermGroup(G));
	    fi;
	    repeat
	       gens := List([1..Size(GeneratorsOfGroup(G))+3],x->Random(H));
	       K := Group(gens);
	    until Size(K) = Size(G);
	    return K;
	end;

## getRandomPc(G) returns a PcGroup that is a random isomorphism copy of G.
getRandomPc := function(G)
	local els, H, rel, p, B, epi, A, i, U, N, hom, el, pcgs;
	   if not IsPcGroup(G) then
	     G := Image(IsomorphismPcGroup(G));
	   fi;
	   els  := [];
	   H    := G;
	   rel  := [];
	   repeat
	      # locate a random normal subgroup of prime index. Such a subgroup
	      # necessarily contains the derived subgroup; so we can just
	      # as well look for a subgroup of prime index in the H/H'
	      p   := Random(Set(Set(AbelianInvariants(H)),x->FactorsInt(x)[1]));
	      N   := PRump(H, p);
	      if Index(H,N) <> p then
              epi := NaturalHomomorphismByNormalSubgroup(H, N);
              A   := Image(epi);
              i   := LogInt(Size(A), p);
              # find a random subgroup of index p
              U := Subgroup(A, List([1..i-1], x -> PseudoRandom(A)));
              while Index(A,U) > p do
                U := ClosureGroup(U, PseudoRandom(A));
              od;
              N := PreImages(epi, U);
          fi;
	      Assert(0, Index(H,N)=p);
	      hom := NaturalHomomorphismByNormalSubgroup(H,N);
	      
	      # The image of hom has prime order, so any non-trivial element
	      # is a generator; we want a random one, so pick any, and then
	      # power it up with a random number coprime to its order
	      el  := First(GeneratorsOfGroup(Image(hom)), x->not IsOne(x));
	      el  := el^Random(1, Order(el)-1);
	      Assert(0, Size(Image(hom)) = p);
	      Assert(0, Order(el) = Size(Image(hom)));
	      Add(els,PreImagesRepresentative(hom,el));
	      Add(rel,Size(Image(hom)));
	      H   := N;
	   until IsTrivial(H);
	   pcgs := PcgsByPcSequence(FamilyObj(els[1]),els);
	   return GroupByPcgs(pcgs);
	end;

## minimal sanity check for large orders
SOTRec.testSOTconst := function(n)
	local all, g, id;
		all := AllSOTGroups(n);
		g := all[Random(1,NumberOfSOTGroups(n))];
		id := IdSOTGroup(g);
		if not IsIsomorphicSOTGroups(g, SOTGroup(id[1],id[2])) then
          Error("Revise p4q.");
		fi;
	end;

## SOTRec.testIdSOTGroup(n) tests whether the same isomorphism type (given as random isomorphic copies of permutation groups) has the same SOT-group ID.
## test against SOT itself
SOTRec.testIdSOTGroup := function(orders)
    local n, nr, gap, sot, soty, i, copies,  gapid, new, signature;
    if IsInt(orders) then
        orders := [orders];
    fi;
    for n in orders do
        if not IsSOTAvailable(n) then
            continue;
        fi;
        nr  := NumberOfSOTGroups(n);
        gap := SmallGroupsAvailable(n) and IdGroupsAvailable(n);
        Print("order ", n, ": testing ", nr, " groups\n");

        sot := List([1..nr],x->SOTGroup(n,x));
        soty := AllSOTGroups(n);
        signature := SortedList(List(Collected(Factors(n)),x->x[2]));
        for i in [1..nr] do
            Assert(0, HasIdSOTGroup(sot[i]));
            Assert(0, HasIdSOTGroup(soty[i]));
            copies := [];
            if IsPermGroup(sot[i]) then
                Assert(0, sot[i] = soty[i]);
            else
                Assert(0, CodePcGroup(sot[i]) = CodePcGroup(soty[i]));
            fi;
            if n < 5000 then
                Add(copies, getRandomPerm(sot[i]));
                if IsSolvableGroup(sot[i]) then
                    Add(copies, getRandomPc(sot[i]));
                fi;
            else
                Add(copies, getRandomPc(sot[i]));
            fi;

            if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then
                Error("Revise SOT ID", [n,i]);
            fi;
        od;

        ## can compare with gap library?
        if gap then
            gapid := List(sot,IdSmallGroup);
            if not Size(gapid) = NumberSmallGroups(n) then
                Error("Revise enumeration.");
            fi;
            if not IsDuplicateFreeList(gapid) then
                Error("Revise ID and construction.");
            fi;
            new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
            if not IsDuplicateFreeList(new) then
                Error("Revise SOT ID.");
            fi;
        fi;
    od;
end;

# variant of SOTRec.testIdSOTGroup that avoids getRandomPerm and getRandomPc
# for cases where those are too slow
SOTRec.testIdSOTGroupCheap := function(orders)
    local n, nr, gap, sot, soty, i, copies,  gapid, new;
    if IsInt(orders) then
      orders := [orders];
    fi;
    for n in orders do
        if not IsSOTAvailable(n) then
            continue;
        fi;
        nr  := NumberOfSOTGroups(n);
        gap := SmallGroupsAvailable(n) and IdGroupsAvailable(n);
        Print("order ", n, ": testing ", nr, " groups\n");

        sot := List([1..nr],x->SOTGroup(n,x));
        soty := AllSOTGroups(n);
        for i in [1..nr] do
            Assert(0, HasIdSOTGroup(sot[i]));
            Assert(0, HasIdSOTGroup(soty[i]));
            copies := [];
            Add(copies, PcGroupCode(CodePcGroup(sot[i]), n));
            Add(copies, PcGroupCode(CodePcGroup(soty[i]), n));

            if not ForAll(copies,x->IdSOTGroup(x)=[n,i]) then
                Error("Revise SOT ID", [n,i]);
            fi;
        od;

        ## can compare with gap library?
        if gap then
            gapid := List(sot,IdSmallGroup);
            if not Size(gapid) = NumberSmallGroups(n) then
                Error("Revise enumeration.");
            fi;
            if not IsDuplicateFreeList(gapid) then
                Error("Revise ID and construction.");
            fi;
            new := List([1..nr],x->IdSOTGroup(SmallGroup(n,x)));
            if not IsDuplicateFreeList(new) then
                Error("Revise SOT ID.");
            fi;
        fi;
    od;
end;
