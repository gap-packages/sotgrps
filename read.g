#############################################################################
##
#W    read.g
##
##


#############################################################################
##
##
##
msg := rec();
ReadPackage(mysmallgrpsPkgName, "gap/msg.gi");                #preliminary functions
ReadPackage(mysmallgrpsPkgName, "gap/pq.gi");                #preliminary functions
ReadPackage(mysmallgrpsPkgName, "gap/p2q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2q2.gi");
ReadPackage(mysmallgrpsPkgName, "gap/pqr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p3q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2qr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/lowpowerPGroups.gi");
ReadPackage(mysmallgrpsPkgName, "gap/SmallGrps.gi");


### quick test against SmallGroups Library
###
msg.testAll := function(from,to)
local todo, i, my, gap;
   todo:=Filtered([from..to], x->msg.isAvailable(x) and (x<2001 or ForAll(Collected(FactorsInt(x)),i->i[2]<3)));;
   for i in todo do Display(i); my:=MySmallGroups(i); gap:=AllSmallGroups(i);
      if not Size(my)=Size(gap) or not AsSet(List(my,IdSmallGroup))=AsSet(List(gap,IdSmallGroup)) then
         Error("ERROR at order ",i,"\n");
      fi;
   od;
   return true;
end;
