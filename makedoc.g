#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;

AutoDoc(rec(
    autodoc := rec(
        files := ["doc/intro.autodoc"],
    ),
    scaffold := true,
    extract_examples := true,
));
