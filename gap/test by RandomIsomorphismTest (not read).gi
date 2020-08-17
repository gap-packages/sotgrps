isp := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [ 1 ] and Length( Factors ( x ) ) < 5;
isp2q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 2, 1 ], [ 1, 2 ] ];
isp2q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [ 2, 2 ];
isp3q := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 3, 1 ], [ 1, 3 ] ];
isp2qr := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ),i -> i[2] ) in [ [ 1, 1, 2 ], [ 1, 2, 1 ], [2, 1, 1] ];
ispqrs := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) = [1, 1, 1, 1];
isp3q2 := x -> IsInt( x ) and x > 1 and List( Collected( FactorsInt( x ) ), i -> i[2] ) in [ [ 2, 3 ], [ 3, 2, ] ];

LoadPackage("mysmallgrps");
LoadPackage("grpconst");

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


good:=Filtered([1..1000000],ispqrs);;

max:=0; maxnr:=0; for i in good do t:=testord(i); if t>max then max:=t; maxnr:=i;  fi; Display([maxnr,max]); Print("----\n");od;




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
