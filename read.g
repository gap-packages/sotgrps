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
DeclareAttribute( "SOTGroup_id", IsGroup );
ReadPackage(sotgrpsPkgName, "gap/sot.gi");                #preliminary functions
ReadPackage(sotgrpsPkgName, "gap/pq.gi");
ReadPackage(sotgrpsPkgName, "gap/p2q.gi");
ReadPackage(sotgrpsPkgName, "gap/p2q2.gi");
ReadPackage(sotgrpsPkgName, "gap/pqr.gi");
ReadPackage(sotgrpsPkgName, "gap/p3q.gi");
ReadPackage(sotgrpsPkgName, "gap/p2qr.gi");
ReadPackage(sotgrpsPkgName, "gap/pqrs.gi");
ReadPackage(sotgrpsPkgName, "gap/p4q.gi");
ReadPackage(sotgrpsPkgName, "gap/lowpowerPGroups.gi");
ReadPackage(sotgrpsPkgName, "gap/SmallGrps.gi");
ReadPackage(sotgrpsPkgName, "gap/IdFunc.gi");
ReadPackage(sotgrpsPkgName, "gap/IdFuncP4Q.gi");
DeclareAttribute( "SOTGroup_id", IsGroup );
Print("This package is currently under development; please report bugs to xpan.eileen@gmail.com. Partial references can be found in the paper GROUPS WHOSE ORDERS FACTORISE INTO AT MOST FOUR PRIMES (https://doi.org/10.1016/j.jsc.2021.04.005) \n");
