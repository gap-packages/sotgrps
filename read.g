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
DeclareAttribute( "MySmallGroup_id", IsGroup );
ReadPackage(mysmallgrpsPkgName, "gap/msg.gi");                #preliminary functions
ReadPackage(mysmallgrpsPkgName, "gap/pq.gi");                #preliminary functions
ReadPackage(mysmallgrpsPkgName, "gap/p2q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2q2.gi");
ReadPackage(mysmallgrpsPkgName, "gap/pqr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p3q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2qr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/pqrs.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p4q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/lowpowerPGroups.gi");
ReadPackage(mysmallgrpsPkgName, "gap/SmallGrps.gi");
ReadPackage(mysmallgrpsPkgName, "gap/IdFunc.gi");
DeclareAttribute( "MySmallGroup_id", IsGroup );
