##
## this is the preliminary code that had been used for tests
##


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
