import csv
from ast import literal_eval as make_tuple
def clean(x):
	
	

	y= x[1:-1].split(",")
	
	

	z = [int(a.strip(' \t\n\r')[:-1]) for a in y]
	return sorted(z)


with open('Peshawa.csv', 'rb') as csvfile:
	spamreader = csv.reader(csvfile, delimiter=',', quotechar='"')
	l= [row for row in spamreader]
	from itertools import groupby
	ll=[list(group) for k, group in groupby(l, lambda x: "Rami" in ",".join(x)) if not k]
	ll =[sum([[x[:3], x[3:]] for x in a], [])  for a in ll]
	ll=[x for x in ll if x!=[]]

	print len(l), "-", len(ll), "\n"
from os import listdir
from os.path import isfile, join
mypath ="/Users/Hoff/Documents/formerdesktop/kaygroups/uploadtuples/PeshawaGAPRecord/M22,g=0,1,2,Gap"
onlyfiles = [f for f in listdir(mypath) if isfile(join(mypath, f))]
def modif(n):
	if "M" in n: return "a"+n
	if "J" in n: return "b"+n
	if "C" in n: return "c"+n
	if "H" in n: return "d"+n

print len(onlyfiles)
headdir ="/Users/Hoff/Documents/formerdesktop/kaygroups/uploadtuples/PeshawaGAPRecord/"
dirs=listdir(headdir)
dirs = [headdir+x for x in dirs] 
listoffiles=[[f for f in listdir(mypath) if isfile(join(mypath, f))] for mypath in dirs if not ".DS_Store" in mypath]
listoffiles=(sum(listoffiles, []))


import re
def gen(x, i) : return re.search("(.*)g=(.*?),(.*).g", x).group(i).strip()
checks = sorted([(gen(x,2),modif(gen(x,1)), gen(x,3).lower(), x) for x in listoffiles])

checks = [ x[3] for x in checks]
results = zip(checks ,ll)

def getlist(a):
	
	types = [clean(x[0]) for x  in a if x[0] != '']
	
	b_set = set(map(tuple,types))
	b = map(list,b_set)
	orderedtypes = sorted(b)
	
	preint = [(x, sum([int(y[1]) for y in a if y[0] != '' and (x == clean(y[0]))]), sum([y[2].split(",") for y in a if y[0] != '' and (x == clean(y[0]))], [])) for x in orderedtypes]
	return [[x[0], x[1], sorted(list(set([int(a) for a in x[2]])))] for x in preint]
s= "Listofresults:=["
for x in results:
	s=s + "rec(name:=\""+x[0]+"\", results := "+str(getlist(x[1]))+"), " 
s=s[:-2]+"];"
print s

f = open('workfile.g', 'w')
f.write(s)
f.close



#listoffiles= sorted(sorted(listoffiles, key = gen))

