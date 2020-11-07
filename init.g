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
sotgrpsPkgName := "sotgrps";

############################################################################
##
#I InfoClass
##
DeclareInfoClass( "InfoMSG" );

#############################################################################
##
#D Read .gd files
##

ReadPackage(sotgrpsPkgName,"gap/SmallGrps.gd");
