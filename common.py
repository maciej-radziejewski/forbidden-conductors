# Settings and code common to all scripts.

B = 300 # Maximum denominator considered.

from collections import defaultdict
from math import gcd, log, isqrt, lcm
from pathlib import Path
import csv
import datetime

class excel_semicolon(csv.excel):
    delimiter = ';'
    quoting = csv.QUOTE_ALL

db_rows = {} # indexed by a, b
db_lack_of_loops = set() # set of: (a, b, length, method)
db_filename = 'loops.csv'
db_lack_of_loops_filename = 'lack_of_loops.csv'
db_requests = set()
db_dirty = False

if Path(db_filename).is_file():
	with open(db_filename, 'r', newline='') as file:
		reader = csv.DictReader(file, dialect=excel_semicolon)
		for row in reader:
			(a, b) = (int(row[label]) for label in ('a', 'b'))
			if int(row['length']) >= 0:
				db_rows[(a, b)] = row.copy()
			else:
				db_requests.add((a,b))

if Path(db_lack_of_loops_filename).is_file():
	with open(db_lack_of_loops_filename, 'r', newline='') as file:
		reader = csv.DictReader(file, dialect=excel_semicolon)
		for row in reader:
			db_lack_of_loops.add (tuple(int(row[label]) for label in ('a', 'b', 'length')))
else:
	with open(db_lack_of_loops_filename, 'w', newline='') as file:
		writer = csv.DictWriter(file, fieldnames=['a', 'b', 'length'], dialect=excel_semicolon)
		writer.writeheader()

def db_entry_exists (a, b):
	return ((a,b) in db_rows)

def db_worth_considering (a, b, length):
	if gcd(a,b) > 1:
		return False
	if db_tried_and_failed (a,b,length):
		return False
	if (a,b) in db_rows:
		entry = db_rows[(a,b)]
		if int(entry['length']) <= length or int(entry['optimal']) == 1:
			return False
	return True

def fraction_str(a, b):
	d = gcd(a,b)
	if b < 0:
		d = -d
	a // d
	b // d
	if b == 1: # this happens also if a == 0
		return str(a)
	elif a > 0:
		return ('\\frac{' + str(a) + '}{' + str(b) + '}')
	else:
		return ('-\\frac{' + str(-a) + '}{' + str(b) + '}')


def db_submit_entry (a, b, loop, weight, method):
	global db_dirty
	length = len(loop)-1
	# A redundant check to make sure our results are right.
	u,v = loop[0],1
	wn,wd = 1,1
	for j in range(length):
		wn *= abs(u)
		wd *= abs(v)
		u,v = v*b,u*a
		u += v*loop[j+1]
	if u != 0:
		print ('Computation error:', loop, 'is not a loop for q =', str(a)+'/'+str(b)+'.')
		exit()
	if type(weight) == tuple:
		if (wn*weight[1])**2 * a**length != (wd*weight[0])**2 * b**length or wn*weight[1]*wd*weight[0] == 0:
			print ('Computation error: weight of', loop, 'seems not to be', fraction_str(weight[0],weight[1]), 'for q =', str(a)+'/'+str(b)+'.')
			exit()
		weight = fraction_str(weight[0],weight[1])
	if wn**2 * a**length == wd**2 * b**length:
		print ('Computation error: unit weight for q =', str(a)+'/'+str(b), 'and', str(loop)+ '.')
		exit()
	if min(wn,wd) == 0:
		print ('Computation error: unexpected weight for q =', str(a)+'/'+str(b), 'and', str(loop)+ '.')
		exit()
	if db_worth_considering (a, b, length):
		is_optimal = 1 if ((length <= 2) or db_tried_and_failed (a,b,length-2)) else 0
		db_rows[(a,b)] = {'a': a, 'b': b, 'example loop': tuple(loop), 'length': length, 'weight': weight, 'method': method, 'optimal': is_optimal}
	if (a,b) in db_requests:
		db_requests.remove((a,b))
	db_dirty = True

def db_request_checking (a,b):
	if not db_entry_exists (a, b):
		if not (a,b) in db_requests:
			db_requests.add((a,b))

def db_save():
	global db_dirty
	if db_dirty:
		with open(db_filename, 'w', newline='') as file:
			writer = csv.DictWriter(file, fieldnames=['a','b','example loop','length','weight','method', 'optimal'], dialect=excel_semicolon)
			writer.writeheader()
			for key in sorted(db_rows, key=lambda x: (x[1],x[0])):
				writer.writerow(db_rows[key])
			for (a,b) in db_requests:
				writer.writerow({'a': a, 'b': b, 'example loop': tuple(), 'length': -1, 'weight': '', 'method': 0, 'optimal': 0})
		db_dirty = False

def db_tried_and_failed (a,b,length):
	return ((a,b,length) in db_lack_of_loops)

# Record the lack of non-unit loops

def db_record_lack_of_loops (a,b,length):
	if (a,b,length) in db_lack_of_loops:
		return
	db_lack_of_loops.add((a,b,length))
	with open(db_lack_of_loops_filename, 'a', newline='') as file:
		writer = csv.DictWriter(file, fieldnames=['a', 'b', 'length'], dialect=excel_semicolon)
		writer.writerow({'a':a, 'b':b, 'length':length})
	if (a,b) in db_rows:
		entry = db_rows[(a,b)]
		if int(entry['length']) == length+2:
			entry['optimal'] = 1

def db_in_scope (a,b): # For 1 <= a < 4*b, 2 <= b <= B, check if (a,b) is in our scope.
	if gcd(a,b) > 1:
		return False
	if a < 4*b:
		return True
	return False

