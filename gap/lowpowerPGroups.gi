msg.lowpowerPGroups := function(p, k)
	local PG, P2, P3, order8, P4, order16, order81, list;
			if p > 1 and k = 1 then
				list := [msg.groupFromData([ [p] ])];
				return list;
			fi;

			if k = 2 then
				P2 := [ [ [p, p], [1, [2, 1]] ], [ [p, p] ] ];
				list := List(P2, x -> msg.groupFromData(x));
				return list;
			fi;

			if p > 2 and k = 3 then
				P3 := [ [ [p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p], [1, [2, 1]] ], [ [p, p, p] ], [ [p, p, p], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				list := List(P3, x -> msg.groupFromData(x));
				return list;
			elif p = 2 and k = 3 then
				order8 := [ [ [2, 2, 2], [1, [2, 1]], [2, [3, 1]] ], [ [2, 2, 2], [1, [2, 1]] ], [ [2, 2, 2] ], [ [2, 2, 2], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
				list := List(order8, x -> msg.groupFromData(x));
				return list;
			fi;

			if p > 3 and k = 4 then
				P4 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] ];
				list := List(P4, x -> msg.groupFromData(x));
				return list;
			elif p = 3 and k = 4 then
				order81 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
				[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ],
				[ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
				[ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ] ];
				list := List(order81, x -> msg.groupFromData(x));
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
				list := List(order16, x -> msg.groupFromData(x));
				return list;
			fi;

			if k > 4 then
				Error("MySmallGroups is not available for p-groups of order not dividing p^4.");
			fi;
			if p = 1 and k = 1 then
				list := [AbelianGroup([1])];
				return list;
			fi;
end;

######################################
msg.NumberPGroups := function(n)
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
msg.PGroup := function(p, k, i)
	local PG, P2, P3, order8, P4, order16, order81, G;
		if p > 1 then
		PG := [ [p] ];
		P2 := [ [ [p, p], [1, [2, 1]] ], [ [p, p] ] ];
		P3 := [ [ [p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p], [1, [2, 1]] ], [ [p, p, p] ], [ [p, p, p], [2, 1, [2, 1, 3, 1]] ], [ [p, p, p], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
		order8 := [ [ [2, 2, 2], [1, [2, 1]], [2, [3, 1]] ], [ [2, 2, 2], [1, [2, 1]] ], [ [2, 2, 2] ], [ [2, 2, 2], [2, 1, [2, 1, 3, 1]] ], [ [2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ] ];
		P4 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
		[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
		[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]] ],
	  [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
	  [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
	  [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
	  [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ],
	  [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ] ];
		order81 := [ [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ], [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ], [ [p, p, p, p], [1, [2, 1]] ], [ [p, p, p, p] ],
		[ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
		[ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]] ],
	  [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ],
	  [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ],
	  [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ],
	  [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ],
	  [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ],
		[ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ] ];
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
		if k = 1 then
			if i = 1 then G := msg.groupFromData(PG);
			else Error("There is a unique group of prime order up to isomorphism.");
			fi;
		fi;

		if k = 2 then
			if i < 3 then G := msg.groupFromData(P2[i]);
			else Error("There are two groups of prime-squared order up to isomorphism: one is cyclic and the other elementary abelian.");
			fi;
		fi;

		if p > 2 and k = 3 then
			if i < 6 then G := msg.groupFromData(P3[i]);
			else Error("There are five isomorphism types of groups of prime-cubed order.");
			fi;
		elif p = 2 and k = 3 then
			if i < 6 then G := msg.groupFromData(order8[i]);
			else Error("There are five isomorphism types of groups of order 8.");
			fi;
		fi;

		if p > 3 and k = 4 then
			if i < 16 then G := msg.groupFromData(P4[i]);
			else Error("There are 15 isomorphism types of groups of this order.");
			fi;
		elif p = 3 and k = 4 then
			if i < 16 then G := msg.groupFromData(order81[i]);
			else Error("There are 15 isomorphism types of groups of order 81.");
			fi;
		elif p = 2 and k = 4 then
			if i < 15 then G := msg.groupFromData(order16[i]);
			else Error("There are 14 isomorphism types of groups of order 16.");
			fi;
		fi;

		if k > 4 then
			Error("MySmallGroup is not available for p-groups of order not dividing p^4.");
		fi;
	else G := AbelianGroup([1]);
	fi;


	return G;
end;
