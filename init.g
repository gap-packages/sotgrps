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
sotgrpsPkgName := "sotgrps"; # FIXME: this is pointless

############################################################################
##
#I InfoClass
##
DeclareInfoClass( "InfoMSG" ); # FIXME: rename this to something more meaningful

#############################################################################
##
#D Read .gd files
##

ReadPackage(sotgrpsPkgName,"gap/SmallGrps.gd");
