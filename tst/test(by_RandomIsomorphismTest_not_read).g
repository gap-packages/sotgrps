##
## this is the preliminary code that had been used for tests
##
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
###

isp := x -> IsInt( x ) and x > 1 and Length( Collected( FactorsInt( x ) )) = 1 and Length( Factors ( x ) ) < 5;
ispq := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) = [1, 1];
isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 2, 1 ], [ 1, 2 ] ];
ispqr := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) = [1, 1, 1];
isp2q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [ 2, 2 ];
isp3q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 3, 1 ], [ 1, 3 ] ];
isp2qr := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ];
ispqrs := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [1, 1, 1, 1];
isp4q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) in [ [ 1, 4 ], [ 4, 1, ] ];


LoadPackage("sotgrps");
LoadPackage("grpconst");

#p4q: if p = 2, 3, 5, 7 then compare sot groups with GAP SmallGroups Lib, otherwise compare with grpconst list.
SOTRec.testordP4Q := function(x) #test by RandomIsomorphismTest
local t,sot,gap,tg,cd;
   if not isp4q(x) then Error("Wrong input."); fi;
   t := Runtime();
   sot := SOTRec.allGroupsP4Q(x);
   t := Runtime()-t;
   Display(["done",x,Size(sot),t]);
   if x mod 16 = 0 or x mod 81 = 0 or x mod 625 = 0 or x mod 2401 = 0 then
      if not Size(sot)=NumberSmallGroups(x) then Error("Revise enumeration."); fi;
      if not AsSet(List(sot,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("Gulp! Construction contains duplicate(s)!");fi;
   else
      Print("start gap\n");
      tg := Runtime();
      gap := ConstructAllGroups(x);
      tg := Runtime()-tg;
      if not Size(sot)=Size(gap) then Error("nr 2"); fi;
      Display([x,t,tg]);
      cd := List(sot,x->rec(order:=Size(x),code:=CodePcGroup(x)));
      Print("start random\n");
      cd := RandomIsomorphismTest(cd,10);
      if Size(cd)<Size(sot) then Error("random is"); else Print("ok\n");fi;
   fi;
   if not ForAll(sot,i->Order(i)=x) then Error("Group order and input do not match."); fi;
   return t;
end;
#test all p^4q orders up to 10^7; record the order that has worst runtime
p4q:=Filtered([1..10^7],isp4q);;
max:=0; maxnr:=0; for i in p4q do t:=SOTRec.testordP4Q(i); if t>max then max:=t; maxnr:=i;  fi; Display([maxnr,max]); Print("----\n");od;
#standalone test comparing the number of SOTGroups constructed with the theoretical enumeration given by Eick & Moede (2018)
for n in p4q do Print("start ", n,"\n"); if not Size(SOTRec.allGroupsP4Q(n) = SOTRec.NumberGroupsP4Q(n) then Error("revise"); fi; od;

#pqrs
SOTRec.testordPQRS := function(x)
local t,sot,gap,tg,cd;
   if not ispqrs(x) then Error("Wrong input."); fi;
   t := Runtime();
   sot := SOTRec.allGroupsPQRS(x);
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



#p2q2
SOTRec.testordP2Q2 := function(x)
local t,sot, gap,tg,cd;
   if not isp2q2(x) then Error("Wrong input."); fi;
   t := Runtime();
   sot := SOTRec.allGroupsP2Q2(x);
   t := Runtime()-t;
   Display(["done",x,Size(sot),t]);
   if x < 50001 then
      if not Size(sot)=NumberSmallGroups(x) then Error("Revise enumeration."); fi;
      if not AsSet(List(sot,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("gulp");fi;
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

#p2qr
SOTRec.testordP2QR := function(x)
local t,sot,gap,tg,cd;
   if not isp2qr(x) then Error("Wrong input."); fi;
   t := Runtime();
   sot := SOTRec.allGroupsP2QR(x);
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

#test all p^2qr orders up to 50 000; record the order that has worst runtime
p2qr:=Filtered([1..50000],isp2qr);;
max:=0; maxnr:=0; for i in p2qr do t:=SOTRec.testordP2QR(i); if t>max then max:=t; maxnr:=i;  fi; Display([maxnr,max]); Print("----\n");od;
