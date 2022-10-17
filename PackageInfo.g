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
Version     := "1.0",
Date        := "01/01/2021",
ArchiveURL := "http://users.monash.edu.au/~heikod/cubefree/cubefree1.17",# FIXME
ArchiveFormats := ".tar.gz",

Persons := [

 rec(
      LastName      := "Pan",
      FirstNames    := "Eileen",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "eileen.pan@monash.edu",
      WWWHome       := "http://users.monash.edu.au/~heikod/",# FIXME
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

README_URL := "https://github.com/xpan-eileen/sotgrps/blob/master/README.md",
PackageInfoURL := "https://github.com/xpan-eileen/sotgrps",

AbstractHTML :=
"The <span class=\"pkgname\">SOTGrps</span> package contains methods to construct up to isomorphism the groups of a small order type.",

PackageWWWHome := "http://users.monash.edu.au/~heikod/cubefree.html", # FIXME

PackageDoc := rec(
  BookName  := "sotgrps",
  ArchiveURLSubset := ["doc", "htm"],
  HTMLStart := "htm/chapters.htm",   # FIXME: add an actual package manual and documentation, e.g. using AutoDoc
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing the groups of a given order of small order type",
  Autoload  := true),

Dependencies := rec(
  GAP := ">=4.3", # FIXME: really? did you test with that?
  NeededOtherPackages := [],
  SuggestedOtherPackages := [],
  ExternalConditions := [] ),

AvailabilityTest := ReturnTrue,
# FIXME: don't use the banner string to print such information to the user; they may never even see it
BannerString := "SOTGrps: the flag USE_NC is set to turn off consistency checks; set USE_NC := false to turn on consistency checks \nSOTGrps: the flag USE_PCP is set to use PcGroup constructions; set USE_PCP := true to use PcpGroup constructions \n",
Autoload := false,
TestFile := "test.gi",  # FIXME: I assume you mean "gap/test.gi" but that still doesn't quite work... better to look at a few other packages and/or let's talk
Keywords := ["construction of finite groups","identification of finite groups"]

));
