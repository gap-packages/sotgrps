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
Version     := "1.3",
Date        := "29/08/2024", # dd/mm/yyyy format
License     := "GPL-2.0-or-later",

Persons := [

 rec(
      LastName      := "Pan",
      FirstNames    := "Eileen",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "xpan.eileen@gmail.com",
      WWWHome       := "https://xpan-eileen.github.io/about/",
      PostalAddress := Concatenation(
            "School of Mathematics",
            "Monash University\n",
            "VIC 3800\n",
            "Melbourne, Australia" ),
      Place         := "Melbourne",
      Institution   := "Monash University",
 ),
 rec(
      FirstNames    := "Max",
      LastName      := "Horn",
      IsAuthor      := false,
      IsMaintainer  := true,
      Email         := "mhorn@rptu.de",
      WWWHome       := "https://www.quendi.de/math",
      PostalAddress := Concatenation(
            "Fachbereich Mathematik\n",
            "RPTU Kaiserslautern-Landau\n",
            "Gottlieb-Daimler-Straße 48\n",
            "67663 Kaiserslautern\n",
            "Germany" ),
      Place         := "Kaiserslautern, Germany",
      Institution   := "RPTU Kaiserslautern-Landau",
 ),

],

Status := "other",

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/sotgrps",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := "https://gap-packages.github.io/sotgrps/",
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz",

AbstractHTML :=
"The <span class=\"pkgname\">SOTGrps</span> package contains methods to construct up to isomorphism the groups of a small order type.",

PackageDoc := rec(
  BookName  := "SOTGrps",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Constructing and identifying groups of small order type",
),

Dependencies := rec(
  GAP := ">=4.10",
  NeededOtherPackages := [],
  SuggestedOtherPackages := [],
  ExternalConditions := [] ),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",
Keywords := ["construction of finite groups","identification of finite groups"],

AutoDoc := rec(
    entities := rec(
        SmallGrp := "<Package>SmallGrp</Package>" ,
    ),
),

));
