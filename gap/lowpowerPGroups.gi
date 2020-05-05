msg.lowpowerPGroups := function(p, k)
	local l, allGrpsP, allGrpsP2, allGrpsP3, allGrpsP4;
		allGrpsP := function(p)
			local list;
				list := [];
				Add(list, AbelianGroup([p]));
			return list;
		end;
#####################################
		allGrpsP2 := function(p)
			local data1, data2, list;
				list := [];
				data1 := [ [p, p], [1, [2, 1]] ];
				data2 := [ [p, p] ];
				Append(list, [msg.groupFromData(data1), msg.groupFromData(data2)]);
			return list;
		end;
#####################################
		allGrpsP3 := function(p)
			local list, data1, data2, data3, data4, data5;
				list :=[];
				data1 := [ [p, p, p], [1, [2, 1]], [2, [3, 1]] ]; ##cyclic
				data2 := [ [p, p, p], [1, [2, 1]] ]; ##C_{p^2} \times C_p
				data3 := [ [p, p, p] ]; ##elementary abelian
				##case1 is when p =2
				if p = 2 then ##case1 when p =2
					data4 := [ [2, 2, 2], [2, 1, [2, 1, 3, 1]] ];
					data5 := [ [2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
				else 					##case2 when p is odd
					data4 := [ [p, p, p], [2, 1, [2, 1, 3, 1]] ];
					data5 := [ [p, p, p], [1, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
				fi;
				Append(list, [msg.groupFromData(data1), msg.groupFromData(data2), msg.groupFromData(data3), msg.groupFromData(data4), msg.groupFromData(data5)]);
			return list;
		end;
#####################################

		##construct groups of order p^4
		allGrpsP4:=function(p)
			local list, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19, data20;
				list := [];
				data1 := [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [3, [4, 1]] ]; ##cyclic
				data2 := [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]] ]; ##C_{p^3} \times C_p
				data3 := [ [p, p, p, p], [1, [2, 1]], [3, [4, 1]] ]; ##C_{p^2} \times C_{p^2}
				data4 := [ [p, p, p, p], [1, [2, 1]] ]; ##C_{p^2} \times Cp^2
				data5 := [ [p, p, p, p] ]; ##elementary abelian
				Append(list, [msg.groupFromData(data1), msg.groupFromData(data2), msg.groupFromData(data3), msg.groupFromData(data4), msg.groupFromData(data5)]); ##all abelian
				if p > 2 then
				  data6 := [ [p, p, p, p], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ];
					data7 := [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
					data8 := [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 3, 1, 4, 1]] ];
					data9 := [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, 1, 4, 1]] ];
				 data10 := [ [p, p, p, p], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ];
				 data11 := [ [p, p, p, p], [1, [2, 1]], [2, [3, 1]], [4, 1, [3, 1, 4, 1]] ];
				 data12 := [ [p, p, p, p], [1, [4, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
				 data13 := [ [p, p, p, p], [3, 1, [2, 1, 3, 1]] ];
				 data14 := [ [p, p, p, p], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ];
					if p = 3 then
						data15 := [ [p, p, p, p], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]], [4, 1, [3, Int(Z(p)), 4, 1]] ];
					elif p > 3 then
						data15 := [ [p, p, p, p], [1, [2, 1]], [3, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ];
					fi;
				else
					data6 := [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1,[2, 1, 3, 1]], [3, 1,[3, 1, 4, 1]] ];
					data7 := [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1,[2, 1, 4, 1]] ];
					data8 := [ [2, 2, 2, 2], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ];
					data9 := [ [2, 2, 2, 2], [1, [4, 1]], [2, [3, 1]], [3, [4, 1]], [2, 1, [2, 1, 3, 1, 4, 1]], [3, 1, [3, 1, 4, 1]] ];
				 data10 := [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
				 data11 := [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ];
				 data12 := [ [2, 2, 2, 2], [2, [3, 1]], [2, 1, [2, 1, 3, 1]], [4, 1, [3, 1, 4, 1]] ];
				 data13 := [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 3, 1]] ];
				 data14 := [ [2, 2, 2, 2], [1, [3, 1]], [2, [3, 1]], [2, 1, [2, 1, 4, 1]] ];
			 fi;

			 if p > 2 then Append(list, [msg.groupFromData(data6), msg.groupFromData(data7), msg.groupFromData(data8), msg.groupFromData(data9), msg.groupFromData(data10), msg.groupFromData(data11), msg.groupFromData(data12), msg.groupFromData(data13), msg.groupFromData(data14), msg.groupFromData(data15)]);
			 else Append(list, [msg.groupFromData(data6), msg.groupFromData(data7), msg.groupFromData(data8), msg.groupFromData(data9), msg.groupFromData(data10), msg.groupFromData(data11), msg.groupFromData(data12), msg.groupFromData(data13), msg.groupFromData(data14)]);
			 fi;
			 return list;
		 end;
#####################################
			## now by power of p
			if k = 1 then return
			allGrpsP(p); fi;
			if k = 2 then return
			allGrpsP2(p); fi;
			if k = 3 then return
			allGrpsP3(p); fi;
			if k = 4 then return
			allGrpsP4(p); fi;
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
