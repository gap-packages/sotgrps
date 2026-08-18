LoadPackage("SOTGrps");
ReadPackage("sotgrps", "tst/test.gi");

# The expected output is written for SmallGrp 1.7, which names the layer an
# order belongs to where older versions numbered it. Drop this once SmallGrp
# 1.7 is required.
SOTGRPS_TEST_TRANSFORM := function( str )
    return ReplacedString( str, "layer 12 of the SmallGroups library",
                           "the layer \"SOTGrps\"" );
end;

TestDirectory( DirectoriesPackageLibrary("sotgrps", "tst"), rec(exitGAP := true,
            testOptions := rec( compareFunction := "uptowhitespace",
                                transformFunction := SOTGRPS_TEST_TRANSFORM ) ) );
FORCE_QUIT_GAP(1);
