#
# Invoke various tests defined in tst/test.gi
#

#
gap> START_TEST("tests.tst");

#
gap> SOTRec.testNumberOfSOTGroups(1, 50000);
true

#
gap> SOTRec.testIdSOTGroup([2..9]);
order 2: testing 1 groups
order 3: testing 1 groups
order 4: testing 2 groups
order 5: testing 1 groups
order 6: testing 2 groups
order 7: testing 1 groups
order 8: testing 5 groups
order 9: testing 2 groups

#
gap> SOTRec.testIdSOTGroup([10..19]);
order 10: testing 2 groups
order 11: testing 1 groups
order 12: testing 5 groups
order 13: testing 1 groups
order 14: testing 2 groups
order 15: testing 1 groups
order 16: testing 14 groups
order 17: testing 1 groups
order 18: testing 5 groups
order 19: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([20..29]);
order 20: testing 5 groups
order 21: testing 2 groups
order 22: testing 2 groups
order 23: testing 1 groups
order 24: testing 15 groups
order 25: testing 2 groups
order 26: testing 2 groups
order 27: testing 5 groups
order 28: testing 4 groups
order 29: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([30..39]);
order 30: testing 4 groups
order 31: testing 1 groups
order 33: testing 1 groups
order 34: testing 2 groups
order 35: testing 1 groups
order 36: testing 14 groups
order 37: testing 1 groups
order 38: testing 2 groups
order 39: testing 2 groups

#
gap> SOTRec.testIdSOTGroup([40..49]);
order 40: testing 14 groups
order 41: testing 1 groups
order 42: testing 6 groups
order 43: testing 1 groups
order 44: testing 4 groups
order 45: testing 2 groups
order 46: testing 2 groups
order 47: testing 1 groups
order 48: testing 52 groups
order 49: testing 2 groups

#
gap> SOTRec.testIdSOTGroup([50..59]);
order 50: testing 5 groups
order 51: testing 1 groups
order 52: testing 5 groups
order 53: testing 1 groups
order 54: testing 15 groups
order 55: testing 2 groups
order 56: testing 13 groups
order 57: testing 2 groups
order 58: testing 2 groups
order 59: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([60..69]);
order 60: testing 13 groups
order 61: testing 1 groups
order 62: testing 2 groups
order 63: testing 4 groups
order 65: testing 1 groups
order 66: testing 4 groups
order 67: testing 1 groups
order 68: testing 5 groups
order 69: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([70..79]);
order 70: testing 4 groups
order 71: testing 1 groups
order 73: testing 1 groups
order 74: testing 2 groups
order 75: testing 3 groups
order 76: testing 4 groups
order 77: testing 1 groups
order 78: testing 6 groups
order 79: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([80..89]);
order 80: testing 52 groups
order 81: testing 15 groups
order 82: testing 2 groups
order 83: testing 1 groups
order 84: testing 15 groups
order 85: testing 1 groups
order 86: testing 2 groups
order 87: testing 1 groups
order 88: testing 12 groups
order 89: testing 1 groups

#
gap> SOTRec.testIdSOTGroup([90..100]);
order 90: testing 10 groups
order 91: testing 1 groups
order 92: testing 4 groups
order 93: testing 2 groups
order 94: testing 2 groups
order 95: testing 1 groups
order 97: testing 1 groups
order 98: testing 5 groups
order 99: testing 2 groups
order 100: testing 16 groups

#
gap> SOTRec.testtranslation(60,80);
order 735: testing 6 groups
order 738: testing 10 groups
order 740: testing 15 groups
order 748: testing 11 groups
order 774: testing 16 groups
order 804: testing 15 groups
order 812: testing 16 groups
order 819: testing 11 groups
order 820: testing 20 groups
order 825: testing 5 groups
order 836: testing 9 groups
order 846: testing 10 groups
order 850: testing 10 groups
order 852: testing 10 groups
order 855: testing 5 groups
order 860: testing 11 groups
order 868: testing 9 groups
order 876: testing 18 groups
order 884: testing 15 groups
order 940: testing 11 groups
order 948: testing 15 groups
true

#
gap> SOTRec.testIdSOTGroup(112);
order 112: testing 43 groups
gap> SOTRec.testIdSOTGroup(162);
order 162: testing 55 groups
gap> SOTRec.testIdSOTGroup(225);
order 225: testing 6 groups
gap> SOTRec.testIdSOTGroup(272);
order 272: testing 54 groups
gap> SOTRec.testIdSOTGroup(330);
order 330: testing 12 groups
gap> SOTRec.testIdSOTGroup(390);
order 390: testing 12 groups
gap> SOTRec.testIdSOTGroup(405);
order 405: testing 16 groups
gap> SOTRec.testIdSOTGroup(496);
order 496: testing 42 groups
gap> SOTRec.testIdSOTGroup(625);
order 625: testing 15 groups
gap> SOTRec.testIdSOTGroup(1053);
order 1053: testing 51 groups
gap> SOTRec.testIdSOTGroup(1806);
order 1806: testing 30 groups
gap> SOTRec.testIdSOTGroup(1875);
order 1875: testing 21 groups
gap> SOTRec.testIdSOTGroup(1911);
order 1911: testing 15 groups
gap> SOTRec.testIdSOTGroup(6875);
order 6875: testing 59 groups
gap> SOTRec.testIdSOTGroup(7203);
order 7203: testing 69 groups
gap> SOTRec.testIdSOTGroup(13203);
order 13203: testing 63 groups
gap> SOTRec.testIdSOTGroup(73205);
order 73205: testing 110 groups
gap> SOTRec.testIdSOTGroup(199927);
order 199927: testing 22 groups

#
gap> SOTRec.testIdSOTGroupCheap(102576253);
order 102576253: testing 446 groups
gap> SOTRec.testIdSOTGroupCheap(4950967);
order 4950967: testing 166 groups
gap> SOTRec.testIdSOTGroupCheap(3262539);
order 3262539: testing 61 groups

#
gap> SOTRec.testIdSOTGroup(150);
order 150: testing 13 groups
gap> SOTRec.testIdSOTGroup(156);
order 156: testing 18 groups
gap> SOTRec.testIdSOTGroup(260);
order 260: testing 15 groups
gap> SOTRec.testIdSOTGroup(294);
order 294: testing 23 groups
gap> SOTRec.testIdSOTGroup(1815);
order 1815: testing 9 groups
gap> SOTRec.testIdSOTGroup(1911);
order 1911: testing 15 groups
gap> SOTRec.testIdSOTGroup(5415);
order 5415: testing 8 groups
gap> SOTRec.testIdSOTGroup(6321);
order 6321: testing 22 groups
gap> SOTRec.testIdSOTGroup(12615);
order 12615: testing 5 groups
gap> SOTRec.testIdSOTGroup(14415);
order 14415: testing 26 groups
gap> SOTRec.testIdSOTGroup(18755);
order 18755: testing 27 groups
gap> SOTRec.testIdSOTGroup(38829);
order 38829: testing 40 groups

#
gap> SOTRec.testIdSOTGroup([147,375,2943,6655]);
order 147: testing 6 groups
order 375: testing 7 groups
order 2943: testing 16 groups
order 6655: testing 26 groups

#
gap> SOTRec.testIdSOTGroup([1444,2601,3249,176435]);
order 1444: testing 12 groups
order 2601: testing 7 groups
order 3249: testing 21 groups
order 176435: testing 40 groups
gap> SOTRec.testIdSOTGroup(255025);
order 255025: testing 32 groups
gap> SOTRec.testIdSOTGroup(555025);
order 555025: testing 7 groups
gap> SOTRec.testIdSOTGroup(1901641);
order 1901641: testing 47 groups

#
gap> STOP_TEST("tests.tst", 1);
