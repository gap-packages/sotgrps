LoadPackage("SOTGrps");
ReadPackage("sotgrps", "tst/test.gi");
TestDirectory( DirectoriesPackageLibrary("sotgrps", "tst"), rec(exitGAP := true,
            testOptions := rec( compareFunction := "uptowhitespace" ) ) );
FORCE_QUIT_GAP(1);
