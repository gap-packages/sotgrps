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

ReadPackage(mysmallgrpsPkgName,"gap/SmallGrps.gd");
