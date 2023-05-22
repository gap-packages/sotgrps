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
true

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
true

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
true

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
true

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
true

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
true

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
true

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
true

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
true

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
true

#
gap> SOTRec.testIdSOTGroup([330,390,1806]);
order 330: testing 12 groups
order 390: testing 12 groups
order 1806: testing 30 groups
true

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
gap> STOP_TEST("tests.tst", 1);
