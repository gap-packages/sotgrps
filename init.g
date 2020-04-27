#############################################################################
##
#W    init.g
#W
##


#############################################################################
##
## Put the name of the package into a single variable.  This makes it
## easer to change it to something else if necessary.
##
mysmallgrpsPkgName := "mysmallgrps";

############################################################################
##
#I InfoClass
##
DeclareInfoClass( "InfoMSG" );

#############################################################################
##
#D Read .gd files
##
ReadPackage(mysmallgrpsPkgName,"gap/pq.gd");                #preliminary functions
ReadPackage(mysmallgrpsPkgName,"gap/p2q.gd");
ReadPackage(mysmallgrpsPkgName,"gap/p2q2.gd");
ReadPackage(mysmallgrpsPkgName,"gap/pqr.gd");
ReadPackage(mysmallgrpsPkgName,"gap/p3q.gd");
ReadPackage(mysmallgrpsPkgName,"gap/p2qr.gd");
ReadPackage(mysmallgrpsPkgName,"gap/lowpowerPGroups.gd");
ReadPackage(mysmallgrpsPkgName,"gap/SmallGrps.gd");
