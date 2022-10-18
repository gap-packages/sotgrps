LoadPackage("SOTGrps");
# run some sanity tests
TestDirectory( DirectoriesPackageLibrary("sotgrps", "tst"), rec(exitGAP := true,
            testOptions := rec( compareFunction := "uptowhitespace" ) ) );
FORCE_QUIT_GAP(1);
