getdata:=function(ss)
local aa,i,li;
aa:=[];

for i in ss do 
	li := Filtered(LL, x-> i=SortedList(List(x.tuple, a->Order(a))));
	Append(aa, [[i, Length(li), Set(List(li, x->x.lengthofbriadorbit))]]);
od;
return aa; end;

processfile:=function(dir, file)
local ss, aa,li, i ,s;

Read(Concatenation(dir, "/", file)); 
ss:=Set(List(LL, x->SortedList(List(x.tuple, a->Order(a)))));
aa:=getdata(ss);
s:=Filtered(Listofresults, x->x.name=file)[1].results;;

if Length(aa)<>Length(s) then
	Print(file, "   the two do not have the same number of tuple types, the gap file has ", Length(aa), "many tuple types and the thesis has ", Length(s), "\n");

	else if Length(LL) <> Sum((List(s, x->x[2]))) then
		Print(file, " there are ", Length(LL), " tuples in the gap file but ", Sum((List(s, x->x[2]))), " in the tehsis\n");
	
		else for i in [1.. Length(aa)] do
			if aa[i]<>s[i] then
				Print(file, " for the tuple number", i, " the thesis sum is ", s[i], " and the gap sum is ", aa[i], "\n") ;
			
	fi;
			od;
		fi;
			fi;
return "done";
end;
procesdir:=function(d)
local dir, f;
for dir in DirectoryContents(d) do     
	if dir <> "." and dir<>".." and dir<>".DS_Store"  then
	dir:=Concatenation(d,"/", dir); 
	for f in DirectoryContents(dir) do
		if f <>"." and f<>".." then 
			processfile(dir,f); 
		fi;
	od;
	fi;od; 
return "done";
end;                         