#############################################################################
##
#W  PackageInfo.g
##
##
##  Based on Frank Luebeck's template for PackageInfo.g.
##

SetPackageInfo( rec(

PackageName := "sotgrps",
Subtitle    := "Constructing the Groups of a Given Small Order Type",
Version     := "0",
Date        := "01/01/2020",
ArchiveURL := "http://users.monash.edu.au/~heikod/cubefree/cubefree1.17",
ArchiveFormats := ".tar.gz",

Persons := [

 rec(
      LastName      := "Pan",
      FirstNames    := "Xueyu",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "heiko.dietrich@monash.edu",
      WWWHome       := "http://users.monash.edu.au/~heikod/",
      PostalAddress := Concatenation( [
            "School of Mathematics",
            "Monash University\n",
            "VIC 3800\n Melbourne, Australia" ] ),
      Place         := "Melbourne",
      Institution   := "Monash University"),

],

Status := "other",
CommunicatedBy := "David Joyner (Annapolis)",
AcceptDate := "10/2027",

README_URL := "http://users.monash.edu.au/~heikod/cubefree/README",
PackageInfoURL := "http://users.monash.edu.au/~heikod/cubefree/PackageInfo.g",

AbstractHTML :=
"The <span class=\"pkgname\">Cubefree</span> package contains methods to construct up to isomorphism the groups of a given (reasonable) cubefree order. The main function ConstructAllCFGroups(n) constructs all groups of a given cubefree order n. The function NumberCFGroups(n) counts all groups of a cubefree order n. Furthermore, IrreducibleSubgroupsOfGL(2,q) constructs the irreducible subgroups of GL(2,q), q=p^r, p>=5 prime, up to conjugacy and RewriteAbsolutelyIrreducibleMatrixGroup(G) rewrites the absolutely irreducible matrix group G (over a finite field) over a minimal subfield.",

PackageWWWHome := "http://users.monash.edu.au/~heikod/cubefree.html",

PackageDoc := rec(
  BookName  := "sotgrps",
  ArchiveURLSubset := ["doc", "htm"],
  HTMLStart := "htm/chapters.htm",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing the groups of a given order of small order type",
  Autoload  := true),

Dependencies := rec(
  GAP := ">=4.3",
  NeededOtherPackages := [],
  SuggestedOtherPackages := [],
  ExternalConditions := [] ),

AvailabilityTest := ReturnTrue,
BannerString := "Loading sotgrps 0.4 ... \n",
Autoload := false,
TestFile := "tst/autoTest.tst",
Keywords := ["construction of groups","irreducible matrix subgroups of degree 2"]

));
