#############################################################################
##
#W    read.g
##
##


#############################################################################
##
## Files containing the algorithm to construct and count cubefree groups
##
msg := rec();

ReadPackage(mysmallgrpsPkgName, "gap/pq.gi");                #preliminary functions
ReadPackage(mysmallgrpsPkgName, "gap/p2q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2q2.gi");
ReadPackage(mysmallgrpsPkgName, "gap/pqr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p3q.gi");
ReadPackage(mysmallgrpsPkgName, "gap/p2qr.gi");
ReadPackage(mysmallgrpsPkgName, "gap/lowpowerPGroups.gi");
ReadPackage(mysmallgrpsPkgName, "gap/SmallGrps.gi");
