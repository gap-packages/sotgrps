#############################################################################
##
#W  PackageInfo.g
##
##
##  Based on Frank Luebeck's template for PackageInfo.g.
##

SetPackageInfo( rec(

PackageName := "SOTGrps",
Subtitle    := "Constructing and identifying groups of small order type",
Version     := "1.0",
Date        := "01/01/2021",
ArchiveURL := "https://github.com/xpan-eileen/sotgrps",
ArchiveFormats := ".tar.gz",

Persons := [

 rec(
      LastName      := "Pan",
      FirstNames    := "Eileen",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "xpan.eileen@gmail.com",
      WWWHome       := "https://xpan-eileen.github.io/about/",
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
PackageInfoURL := "https://github.com/xpan-eileen/sotgrps/blob/master/PackageInfo.g",

AbstractHTML :=
"The <span class=\"pkgname\">SOTGrps</span> package contains methods to construct up to isomorphism the groups of a small order type.",

PackageWWWHome := "https://github.com/xpan-eileen/sotgrps",

PackageDoc := rec(
  BookName  := "SOTGrps",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing and identifying groups of small order type",
  Autoload  := true),

Dependencies := rec(
  GAP := ">=4.10",
  NeededOtherPackages := [],
  SuggestedOtherPackages := [],
  ExternalConditions := [] ),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",
Keywords := ["construction of finite groups","identification of finite groups"],

));
