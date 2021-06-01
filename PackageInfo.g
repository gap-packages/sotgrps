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
      FirstNames    := "Eileen",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "eileen.pan@monash.edu",
      WWWHome       := "http://users.monash.edu.au/~heikod/",
      PostalAddress := Concatenation( [
            "School of Mathematics",
            "Monash University\n",
            "VIC 3800\n Melbourne, Australia" ] ),
      Place         := "Melbourne",
      Institution   := "Monash University"),

],

Status := "other",
CommunicatedBy := " (Annapolis)",
AcceptDate := " ",

README_URL := "NA",
PackageInfoURL := "NA",

AbstractHTML :=
"The <span class=\"pkgname\">SOTGrps</span> package contains methods to construct up to isomorphism the groups of a small order type.",

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
BannerString := "SOTGrps: the flag USE_NC is set to turn off consistency checks; set USE_NC := false to turn on consistency checks \nSOTGrps: the flag USE_PCP is set to use PcGroup constructions; set USE_PCP := true to use PcpGroup constructions \n",
Autoload := false,
TestFile := "test.gi",
Keywords := ["construction of finite groups","identification of finite groups"]

));
