##
## this is preliminary code that had been used for testing purposes; please ignore
##

# FIXME: remove this file., or else rename it and place it in another directory

isp := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [ 1 ] and Length( Factors ( x ) ) < 5;
isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 2, 1 ], [ 1, 2 ] ];
isp2q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [ 2, 2 ];
isp3q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 3, 1 ], [ 1, 3 ] ];
isp2qr := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ];
ispqrs := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [1, 1, 1, 1];
isp3q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) in [ [ 2, 3 ], [ 3, 2, ] ];
isp4q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) in [ [ 1, 4 ], [ 4, 1, ] ];


LoadPackage("sotgrps");
LoadPackage("grpconst");

#p4q: if p^4 = 16 or 81 then compare my groups with GAP SmallGroups Lib, otherwise compare with grpconst list.
testord := function(x) #test by RandomIsomorphismTest
local t,my,gap,tg,cd;
   if not isp4q(x) then Error("input"); fi;
   t := Runtime();
   my := msg.allGroupsP4Q(x);
   t := Runtime()-t;
   Display(["done",x,Size(my),t]);
   if x mod 16 = 0 or x mod 81 = 0 then
      if not Size(my)=NumberSmallGroups(x) then Error("nr"); fi;
      if not AsSet(List(my,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("gulp");fi;
   else
      Print("start gap\n");
      tg := Runtime();
      gap := ConstructAllGroups(x);
      tg := Runtime()-tg;
      if not Size(my)=Size(gap) then Error("nr 2"); fi;
      Display([x,t,tg]);
      cd := List(my,x->rec(order:=Size(x),code:=CodePcGroup(x)));
      Print("start random\n");
      cd := RandomIsomorphismTest(cd,10);
      if Size(cd)<Size(my) then Error("random is"); else Print("ok\n");fi;
   fi;
   if not ForAll(my,i->Order(i)=x) then Error("order"); fi;
   return t;
end;
good:=Filtered([1..10000000],isp4q);;
max:=0; maxnr:=0; for i in good do t:=testord(i); if t>max then max:=t; maxnr:=i;  fi; Display([maxnr,max]); Print("----\n");od;
#Also test the number of groups constructed matches theoretical enumeration given by Eick & Moede (2018)
for n in isp4q do Print("start ", n,"\n"); if not Size(msg.allGroupsP4Q(n) = msg.NumberGroupsP4Q(n) then Error("revise"); od;

#pqrs
testord := function(x)
local t,my,gap,tg,cd;

   if not ispqrs(x) then Error("input"); fi;
   t := Runtime();
   my := msg.allGroupsPQRS(x);
   t := Runtime()-t;
   Display(["done",x,Size(my),t]);
   if x < 2001 then
      if not Size(my)=NumberSmallGroups(x) then Error("nr"); fi;
      if not AsSet(List(my,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("gulp");fi;
   else
      Print("start gap\n");
      tg := Runtime();
      gap := ConstructAllGroups(x);
      tg := Runtime()-tg;
      if not Size(my)=Size(gap) then Error("nr 2"); fi;
      Display([x,t,tg]);
      cd := List(my,x->rec(order:=Size(x),code:=CodePcGroup(x)));
      Print("start random\n");
      cd := RandomIsomorphismTest(cd,10);
      if Size(cd)<Size(my) then Error("random is"); else Print("ok\n");fi;

   fi;
   if not ForAll(my,i->Order(i)=x) then Error("order"); fi;
   return t;

end;



#p2q2
testord := function(x)
local t,my,gap,tg,cd;

   if not isp2q2(x) then Error("input"); fi;
   t := Runtime();
   my := allGroupsP2Q2(x);
   t := Runtime()-t;
   Display(["done",x,Size(my),t]);
   if x < 50001 then
      if not Size(my)=NumberSmallGroups(x) then Error("nr"); fi;
      if not AsSet(List(my,IdSmallGroup))=AsSet(List([1..NumberSmallGroups(x)],i->[x,i])) then Error("gulp");fi;
   else
      Print("start gap\n");
      tg := Runtime();
      gap := ConstructAllGroups(x);
      tg := Runtime()-tg;
      if not Size(my)=Size(gap) then Error("nr 2"); fi;
      Display([x,t,tg]);
      cd := List(my,x->rec(order:=Size(x),code:=CodePcGroup(x)));
      Print("start random\n");
      cd := RandomIsomorphismTest(cd,10);
      if Size(cd)<Size(my) then Error("random is"); else Print("ok\n");fi;

   fi;
   if not ForAll(my,i->Order(i)=x) then Error("order"); fi;
   return t;

end;


good:=Filtered([10001..50000],isp2qr);;

max:=0; maxnr:=0; for i in good do t:=testord(i); if t>max then max:=t; maxnr:=i;  fi; Display([maxnr,max]); Print("----\n");od;
