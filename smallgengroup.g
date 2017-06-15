SocleSeries := function(G)
local H, l, hom;
H:=Socle(G);
if H=G then

  return([G]);
else  hom:= NaturalHomomorphismByNormalSubgroup(G,H);
l:=[H];
Append(l,List(SocleSeries(Image(hom)), x->PreImages(hom, x)));
return(l);
fi;
end;

######################

LexValue := function(G, socs, x, truncate)
local ord, lev, i, siz, list;

for i in [1.. Length(socs)] do
if x in socs[i] then lev:=i;break; fi;
od;
ord:=Order(x);
siz:=Order(G)/Order(Centralizer(G,x));
if truncate then
    list:=[ord, siz];
else
    list := [lev, ord, siz];
fi;
if IsPrime(ord) then return list;
else 
for i in (Filtered(DivisorsInt(ord), x->IsPrime(x))) do
  if IsPrimeInt(i) then
    Append(list, LexValue(G, socs, x^(i), truncate));

  fi;

od;
fi;
return list;
end; 
#############
#################
# this computes the lexValue from a GAP character thable
########
StandardLexValue := function(tbl, x)
local ord, lev, i, siz, list;
ord:=OrdersClassRepresentatives(tbl)[x];
siz:=SizesCentralizers(tbl)[1]/SizesCentralizers(tbl)[x];
list := [ord, siz];
if IsPrime(ord) then return list;
else 
for i in (Filtered(DivisorsInt(ord), x->IsPrime(x))) do
  
    Append(list, StandardLexValue(tbl,ComputedPowerMaps(tbl)[i][x]));


od;
fi;
return list;
end;
#################
#This computes the Lexvalues of the ordering from the standard character table.
####
StandardOrderConjugacyClasses:=function(tbl)
local list, socs;
list:=List([1..NrConjugacyClasses(tbl)], x->StandardLexValue(tbl, x));
return list;
end;
#################

OrderConjugacyClasses:=function(G)
local a,b, l,orderlist, standardList, tbl,new, list, socs; socs:=SocleSeries(G);
l:=ReplacedString(Name(G),"(","");
l:=ReplacedString(l,")","");
list:=List(ConjugacyClasses(G), x->Representative(x));
tbl:=CharacterTable(l);
if tbl<>fail then
   new:=CharacterTableWithStoredGroup(G,tbl);
fi;
if tbl<>fail  and new<>fail  then
    
    orderlist:=IdentificationOfConjugacyClasses(new);
    list:=List(orderlist, x->list[x]);
else

   Sort(list, function(a,b) return LexValue(G,socs,a, false)<LexValue(G,socs,b, false); end);
fi;
return list;
end;


#############

renormalizeTuple:= function(elemTuple, positionTuple, r)
local a, pos, len, g, i,ll, botgen;
len:=Length(elemTuple);
botgen:=(len-r)/2;
if r=0 then
    return [elemTuple{[1..2*botgen]},positionTuple{[1..2*botgen]}];
else
a:=Maximum(positionTuple{[(2*botgen+1)..len]});
pos:=Position(positionTuple{[(2*botgen+1)..len]}, a);
g:=elemTuple[2*botgen+pos];

for i in [2*botgen+pos+1..len] do
   elemTuple[i-1]:=g*elemTuple[i]*g^-1;
   positionTuple[i-1]:=positionTuple[i];
od;
ll:=renormalizeTuple(elemTuple{[1..len-1]}, positionTuple{[1..len-1]}, r-1);
Append(ll[1], [g]); Append(ll[2], [a]);
return ll;
fi;
end;


genusTuple:=function(tuple)
local n;
n:=NrMovedPoints(Group(tuple));
return (Sum(List(tuple, x->n-Length(Orbits(Group(x),[1..n]))))-2*(n-1))/2;
end;

############

FindConjugacy:=function(x, listOfClasses, G)
local i;
for i in [1..Length(listOfClasses)] do
    if IsConjugate(G,x, listOfClasses[i]) then
        return i;
        break;
    fi;
od;
end;





CreateGroup:= function(tuple, r, sizeListOfTuples, listOfGroups) ## r is the number of ramification points
    local x, s, normalised, botgen,record, groupForTuple, primGroup, g, iso, notfound, i, prod, filteredListOfGroups;
###### check that it is a proper tuple
    prod:=();

    botgen:=(Length(tuple)-r)/2;
    if not (botgen in Integers) then
	return Error("genus not integral");
    fi;
    for i in [1..botgen] do
        prod:=prod*Comm(tuple[i], tuple[botgen+i]);
    od;
    for i in [2*botgen+1..Length(tuple)] do
        prod:=prod*tuple[i];
    od;
    if prod<>() then
    return Error("Not a real tuple, product not identity");
    fi;
#####
#makes a record and searches for the group/ isom, if found it is appended to the record, otherwise the list of groups is ammended and the iso is the identity
####
    record:=rec(tuple:=tuple, ramification:=r, signature:=[botgen]);
    notfound:=true;
    groupForTuple:=Group(tuple);
    if IsPrimitive(groupForTuple) then
        primGroup:=PrimitiveGroup(NrMovedPoints(groupForTuple), PrimitiveIdentification(groupForTuple));
	filteredListOfGroups:=Filtered(listOfGroups, x->(x.order=Order(primGroup) and x.name=Name(primGroup)));
        for g in filteredListOfGroups do
            iso:=IsomorphismGroups( primGroup, PrimitiveGroup(g.numberOfPoints, g.position));
            if iso<>fail then
                record.groupPosition:=Position(listOfGroups,g);
                record.isomorphism:=iso;
                notfound:=false;
                break;
            fi;
        od;
        if notfound then
            Append(listOfGroups, [rec(order:=Order(primGroup), name:=Name(primGroup), numberOfPoints:=NrMovedPoints(primGroup), position:=PrimitiveIdentification(primGroup),   conjugacyClasses:=OrderConjugacyClasses(primGroup))]);
            record.groupPosition:=Length(listOfGroups);
            record.isomorphism:= IdentityMapping(primGroup);
        fi; 
                
    else 
        return Error("not a primitive group");
    fi;
    record.genus:=genusTuple(record.tuple);
    record.positions:=List(record.tuple, x->FindConjugacy(Image(record.isomorphism,x),listOfGroups[record.groupPosition].conjugacyClasses,  PrimitiveGroup(listOfGroups[record.groupPosition].numberOfPoints, listOfGroups[record.groupPosition].position)));
    normalised:=renormalizeTuple(record.tuple, record.positions, r);
    record.tuple:=normalised[1];
    record.positions:=normalised[2];
record.isomorphism:=MappingGeneratorsImages(record.isomorphism);
    Append(record.signature, List(record.tuple, x->Order(x)));
    x:=record;
  #  s:=Concatenation("curl --user braidorbits:sporadic -d \"genus=",String(x.genus),"&tuple=",String(x.tuple),"&ramification=",String(x.ramification),"&signature=",String(x.signature),"&positions=",String(x.positions),"&isomorphism=",String(x.isomorphism),"&groupposition=",String(x.groupPosition),"&groupname=",listOfGroups[x.groupPosition].name,"\" https://braidorbits.pythonanywhere.com/braid/default/api/tuples.json");
#Exec(s);
    return [record, listOfGroups,sizeListOfTuples] ;
end;

 processJasonFile:=function(file, sizeListOfTuples, listOfGroups, tuples)
local ll,lll, i, a, b, orbs;
    lll:=NamesGVars( );
    for i in lll do
        if Length(i)< 7  and  PositionSublist(i, "Orbit")<>fail  and IsBoundGlobal(i) and IsList(ValueGlobal(i)) then
            UnbindGlobal(i);
        fi;
    od;

    Read(file);

    lll:=NamesGVars( );
    if PositionSublist(file, "new")<>fail then
        
        orbs:=myOrbits;
        Print("found one", Length(orbs));
        for a in orbs do
                                                         
             ll:=CreateGroup(a,Length(a), sizeListOfTuples, listOfGroups);
             Append(tuples, [ll[1]]);
             sizeListOfTuples:=sizeListOfTuples+1;
        od;
     else  
         orbs:=Filtered(lll, x->Length(x)< 7  and  PositionSublist(x, "Orbit")<>fail and IsBoundGlobal(x) and IsList(ValueGlobal(x)));
         for a in orbs do
         Print(a, Length(ValueGlobal(a)), "\n");

         b := ValueGlobal(a)[1];                                              
         ll:=CreateGroup(b,Length(b), sizeListOfTuples, listOfGroups);
         Append(tuples, [ll[1]]);
         sizeListOfTuples:=sizeListOfTuples+1;
        
         od;
     fi;
    Print(Length(tuples), "\n");
    return [tuples, sizeListOfTuples];
end;

procesdir:=function(dir,sizeListOfTuples, listOfGroups,tuples)
local a,b;
for a in DirectoryContents(dir) do
    if a<>"." and a<>".." and IsDirectoryPath(Concatenation(dir,a)) then
        procesdir(Concatenation(dir,a,"/"),sizeListOfTuples, listOfGroups,tuples);
    elif PositionSublist(a, "GeneratingType")<>fail then
        Print(Concatenation(dir,a, "\n"));
        processJasonFile(Concatenation(dir,a), sizeListOfTuples, listOfGroups, tuples);
        sizeListOfTuples:=Length(tuples);
    fi;

od;
end;
lookUp:=function(arg)
local a,b,c,d;
LoadPackage("IO");
ReadWeb("http://hoff.x10host.com/nextry/listofgroups");
ReadWeb("http://hoff.x10host.com/nextry/listoftuples");
a:=Length(arg)/2;

if IsInt(a) then
    c:=tuples;
    b:=Position(arg, "groupPosition");
    
    Print(b);
    if b<>fail then
        
        c:= Filtered(c, x->x.groupPosition=arg[b+1]);
    
    fi;
    b:=Position(arg, "genus");
    
    Print(b);
    if b<>fail then
        
        c:= Filtered(c, x->x.genus=arg[b+1]);
    
    fi;
    b:=Position(arg, "ramification");
    
    Print(b);
    if b<>fail then
        
        c:= Filtered(c, x->x.ramification=arg[b+1]);
    
    fi;
    b:=Position(arg, "signature");
    
    Print(b);
    if b<>fail then
        

        c:= Filtered(c, x->PermListList(x.signature,arg[b+1])<>fail);
    
    fi;
return c;
else 
Error("bad format");
fi;end;

dir:="/Users/Hoff/Downloads/jasonsfiles/";
listOfGroups:=[]; tuples:=[];sizeListOfTuples:=0;
procesdir(dir,sizeListOfTuples, listOfGroups,tuples);
 PrintTo("listoftuples","tuples:=", tuples, ";");
 PrintTo("listofgroups","listOfGroups:=", String(listOfGroups), ";");
 Exec("python bb.py listofgroups");
 Exec("python bb.py listoftuples");



AppendTo(out, Concatenation(String(x.tuple), "|", String(x.isomorphism), "|", String(x.positions), "|", String(x.genus), "|", String(x.groupPosition),"|",String( listOfGroups[x.groupPosition].name),  "|",String(x.ramification), "|", String(x.signature), "\n"));

for x in tuples do
#s:=Concatenation("curl --user braidorbits:sporadic -d \"genus=",String(x.genus),"&tuple=",String(x.tuple),"&ramification=",String(x.ramification),"&signature=",String(x.signature),"&positions=",String(x.positions),"&isomorphism=",String(x.isomorphism),"&groupposition=",String(x.groupPosition),"&groupname=",listOfGroups[x.groupPosition].name,"\" https://braidorbits.pythonanywhere.com/braid/default/api/tuples.json");
Exec(s);
od;
listOfGroups;
 f := SingleHTTPRequest( domain, 80, "GET", uri, rec(), false, false );
Syntax error, unexpected identifier, expecting ';'
Syntax error, unexpected identifier, expecting ';'
Syntax error