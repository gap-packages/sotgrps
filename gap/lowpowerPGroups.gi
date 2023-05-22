## Construction of p-groups of order dividing p^4
## Such low-power p-groups are well-known; our construction uses iterative extensions.
## For further details of the classification of groups of order p^4, we also refer to Alder, Garlow, Wheland's paper "Groups of order p^4 made less difficult" arXiv:1611.00461
####################################
SOTRec.lowpowerPGroups := function(arg)
	local p, k, PG, P2, P3, order8, r, P4, order16, order81, list;
			p := arg[1];
			k := arg[2];
			if p > 1 and k = 1 then
				if Length(arg) = 2 then
					list := [SOTRec.groupFromData([ [p] ])];
				else
					list := [ [ [p] ] ];
				fi;
				return list;
			fi;

			if k = 2 then
				P2 := [ [ [p, p], [1, [2, 1]] ], [ [p, p] ] ];
				if Length(arg) = 2 then
					list := List(P2, x -> SOTRec.groupFromData(x));
				else
					list := P2;
				fi;
				return list;
			fi;

			if p > 2 and k = 3 then
				P3 := [ [ [p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p], [1, [2, 1]] ], [ [p, p, p] ], [ [p, p, p], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				if Length(arg) = 2 then
					list := List(P3, x -> SOTRec.groupFromData(x));
				else
					list := P3;
				fi;
				return list;
			elif p = 2 and k = 3 then
				order8 := [ [ [2, 2, 2], [1, [2, 1]], [2, [3, 1]] ], [ [2, 2, 2], [1, [2, 1]] ], [ [2, 2, 2] ], [ [2, 2, 2], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				if Length(arg) = 2 then
					list := List(order8, x -> SOTRec.groupFromData(x));
				else
					list := order8;
				fi;
				return list;
			fi;

			if p > 3 and k = 4 then
				r := Int(Z(p));
				P4 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] ];
				if Length(arg) = 2 then
					list := List(P4, x -> SOTRec.groupFromData(x));
				else
					list := P4;
				fi;
				return list;
			elif p = 3 and k = 4 then
				order81 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 2, 4, 1]] ] ];
				if Length(arg) = 2 then
					list := List(order81, x -> SOTRec.groupFromData(x));
				else
					list := order81;
				fi;
				return list;
			elif p = 2 and k = 4 then
				order16 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1,[2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1,[2, 1, 3, 1]], [3, 1,[3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ] ];
				if Length(arg) = 2 then
					list := List(order16, x -> SOTRec.groupFromData(x));
				else
					list := order16;
				fi;
				return list;
			elif k > 4 then
				Error("AllSOTGroups is not available for p-groups of order not dividing p^4.");
			elif p = 1 and k = 1 then
				list := [AbelianGroup([1])];
				return list;
			fi;
end;

######################################
SOTRec.NumberPGroups := function(n)
	local power, prime, w;
		prime := Collected(Factors(n))[1][1];
		power := Collected(Factors(n))[1][2];
		if power = 1 then w := 1; fi;
		if power = 2 then w := 2; fi;
		if power = 3 then w := 5;	fi;
		if power = 4 and prime = 2 then w := 14; fi;
		if power = 4 and prime > 2 then w := 15; fi;
	return w;
end;
#####################################
SOTRec.PGroup := function(arg)
	local p, k, i, PG, P2, P3, order8, P4, order16, order81, r, G;
		p := arg[1]; k := arg[2]; i := arg[3];
		if p > 1 then
			if k = 1 then
				PG := [ [p] ];
				if i = 1 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(PG);
					elif Length(arg) = 4 then
						G := PG;
					fi;
				else Error("There is a unique group of prime order up to isomorphism.");
				fi;
			fi;

			if k = 2 then
				P2 := [ [ [p, p], [1, [2, 1]] ], [ [p, p] ] ];
				if i < 3 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(P2[i]);
					elif Length(arg) = 4 then
						G := P2[i];
					fi;
				else Error("There are two groups of prime-squared order up to isomorphism: one is cyclic and the other elementary abelian.");
				fi;
			fi;

			if p > 2 and k = 3 then
				P3 := [ [ [p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p], [1, [2, 1]] ], [ [p, p, p] ], [ [p, p, p], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				if i < 6 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(P3[i]);
					elif Length(arg) = 4 then
						G := P3[i];
					fi;
				else Error("There are five isomorphism types of groups of prime-cubed order.");
				fi;
			elif p = 2 and k = 3 then
				order8 := [ [ [2, 2, 2], [1, [2, 1]], [2, [3, 1]] ], [ [2, 2, 2], [1, [2, 1]] ], [ [2, 2, 2] ], [ [2, 2, 2], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				if i < 6 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(order8[i]);
					elif Length(arg) = 4 then
						G := order8[i];
					fi;
				else Error("There are five isomorphism types of groups of order 8.");
				fi;
			fi;

			if p > 3 and k = 4 then
				r := Int(Z(p));
				P4 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] ];
				if i < 16 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(P4[i]);
					elif Length(arg) = 4 then
						G := P4[i];
					fi;
				else Error("There are 15 isomorphism types of groups of this order.");
				fi;
			elif p = 3 and k = 4 then
				r := Int(Z(p));
				order81 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, r, 4, 1]] ] ];
				if i < 16 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(order81[i]);
					elif Length(arg) = 4 then
						G := order81[i];
					fi;
				else Error("There are 15 isomorphism types of groups of order 81.");
				fi;
			elif p = 2 and k = 4 then
				order16 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1]], [3, 1, [3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ],
				[ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ] ];
				if i < 15 then
					if Length(arg) = 3 then
						G := SOTRec.groupFromData(order16[i]);
					elif Length(arg) = 4 then
						G := order16[i];
					fi;
				else Error("There are 14 isomorphism types of groups of order 16.");
				fi;
			fi;

			if k > 4 then
				Error("SOTGroup is not available for p-groups of order not dividing p^4.");
			fi;
		else G := AbelianGroup([1]);
		fi;
	return G;
end;
