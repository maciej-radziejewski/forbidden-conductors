# Find loops for q=a/b with given a and b
# by looking for pairs of paths with matching endpoints.
# We restrict the search to paths such that the endpoints of all subpaths
# are in an interval [-C/2,C/2], where C is an integer.
# This gives about C choices for the next m_k given m_0, ..., m_{k-1}.
# We will be storing and comparing thousands of paths.
# Keeping a sequence of m_i's for each costs a lot of memory, especially that m_i's
# may get large. Instead, we store paths encoded as large integers,
# whose digits (in an appropriate base) correspond to the unit intervals
# chosen at each iteration.
# The encoding p for a path m is such that -p corresponds to the sequence of -m_i.
# We use signed 'digits' e in (-base+1)/2, ..., (base-1)/2,
# where base is an odd integer, the smallest such that base > C.
# Let u/av be the partial endpoint (similar notation is used in the paper).
# The digit corresponds to u/av as follows:
# Only 0/1 maps to 0, positive u/av maps to ceiling(u/av), negative to floor(u/av).
# For a loop the top-significance digit is zero, making it undetectable.
# In that case, for non-zero loops, we add an extra digit 1 'over the top'.

from common import *
current_method = int(Path(__file__).stem.split('_')[0])
# import psutil

# This function is here only for testing.
# It is not written to be efficient, but to mimic the behaviour of find_loop().
def encode_path (a, b, C, ms):
	if not ms:
		return 0
	base = C+1+(C%2)
	sig = base
	p = ms[0]
	u = p*a
	v = 1
	if 2*abs(p) > C:
		print ('Value', ms[0], 'has absolute value greater than', C, 'for', a, b, C, ms, i)	
	for i in range(1,len(ms)):
		uu,vv = a*b*v,u
		d = gcd(uu,vv)
		if vv < 0:
			d = -d
		uu //= d
		vv //= d
		if uu % (a*vv) == 0: # uu/a vv is an integer
			m_begin = -uu // (a*vv) # The first (and only) value of m in this case.
			m_end = 1 + m_begin
			m_skip = m_end # This means no 'digit skipping', see below.
			e = 0
		elif (2*uu) % (a*vv) != 0:
			m_begin = -((C*a*vv + 2*uu)//(2*a*vv))
			m_end = m_begin + C
			m_skip = 1 + (-uu)//(a*vv)
			e = uu//(a*vv) + m_begin
		else: # uu/a vv = 1/2 + integer
			m_begin = (a*vv - 2*uu)//(2*a*vv) # The first endpoint will be 1/2.
			m_end = m_begin + (C+1)//2
			m_skip = m_begin
			e = 0 # Ok, we could start with 1 and avoid skipping, but it will happen if we reverse digits.
		m_found = False
		for m in range(m_begin, m_end):
			if m == m_skip:
				e += 1
			if m == 0:
				continue # We only look for proper loops.
			if m == ms[i]:
				u = uu + m*a*vv
				v = vv
				p += e*sig
				m_found = True
				break
		if not m_found:
			print ('Value', ms[i], 'not in range', range(m_begin, m_end), 'for', a, b, C, ms, i)
		sig *= base
	if ms[-1] == 0:
		p += sig
	return p


def decode_path (a, b, C, p):
	if not p:
		return [0]
	base = C+1+(C%2)
	sig = base
	e = p % base
	if e+e > base:
		e -= base
	p -= e
	ms = [e]
	u = e*a
	v = 1
	while p:
		p //= base
		e = p % base
		if e+e > base:
			e -= base
		uu,vv = a*b*v,u
		d = gcd(uu,vv)
		if vv < 0:
			d = -d
		uu //= d
		vv //= d
		if uu % (a*vv) == 0: # uu/a vv is an integer
			if e != 0:
				print ('Internal error decoding a path (loop terminated with a non-zero digit)', a, b, C, p, e, uu, vv)
				exit()
			if p != base:
				print ('Internal error decoding a path (improper ending after digit 0)', a, b, C, p, e, uu, vv)
				exit()
			p = 0
			m = -uu // (a*vv)
			ms.append(m)
			u = uu + m*a*vv
			v = vv
		else:
			if e == 0:
				print ('Internal error decoding a path (0 digit in a non-loop)', a, b, C, p, e, uu, vv)
				exit()
			if (2*uu) % (a*vv) != 0:
				m_begin = -((C*a*vv + 2*uu)//(2*a*vv))
				m_end = m_begin + C
				m_skip = 1 + (-uu)//(a*vv)
				m = e - (uu//(a*vv))
			else: # uu/a vv = 1/2 + integer
				m_begin = (a*vv - 2*uu)//(2*a*vv)
				m_end = m_begin + (C+1)//2
				m_skip = m_begin
				m = e + m_begin
				m_begin -= (C+1)//2 # Digits could have been inverted.
			if m > m_skip:
				m -= 1
			elif m == m_skip:
				print ('Internal error decoding a path (skipping error)', a, b, C, p, e, uu, vv)
				exit()
			if m < m_begin or m >= m_end:
				print ('Internal error decoding a path (range error)', a, b, C, p, e, uu, vv)
				exit()
			if m == 0 and p != e: # We might have m == 0 at the very end.
				print ('Internal error decoding a path (improper path)', a, b, C, p, e, uu, vv)
				exit()
			p -= e
			ms.append(m)
			u = uu + m*a*vv
			v = vv
	return ms

# This one works for paths of even length.
def weight (a,b,m):
	if len(m) <= 1:
		return 1,1
	u, v = 0,1
	wn,wd = 1,1
	k = len(m)-1
	for i in range(k):
		u += a*v*m[i]
		wn *= abs(u)
		wd *= abs(v)
		d = gcd(wn,wd)
		wn //= d
		wd //= d
		u,v = a*b*v,u
		d = gcd(u,v)
		u //= d
		v //= d
	wd *= (a*b)**(k//2)
	d = gcd(wn,wd)
	wn //= d
	wd //= d
	return ((wn,wd))


def report_loop (a, b, loop):
	# Propagate results from q=a/b to all q/n,
	# using one of the propositions in the paper.
	div_a = set()
	d = 1
	while d*d <= a:
		if a % d == 0:
			div_a.add (d)
			div_a.add (a//d)
		d += 1
	div_a -= {a}
	k = len(loop)//2
	for d1 in div_a:
		for d2 in range (1,1+B//b):
			if gcd(a//d1,d2) == 1:
				aa = a//d1
				bb = b*d2
				if db_worth_considering(aa,bb, len(loop)-1):
					new_loop = loop.copy()
					for j in range (k):
						new_loop[2*j+1] *= (d1*d2)
					db_submit_entry (aa, bb, new_loop, weight(aa,bb, new_loop), current_method)

def time_elapsed():
	global t1
	t2 = datetime.datetime.now()
	return int((t2 - t1).total_seconds())

def report_pair (a, b, C, p1, p2):
	p1 = decode_path(a,b,C,p1)
	p2 = decode_path(a,b,C,p2)
	loop = [0] * (len(p1)+len(p2)-1)
	print ('\033[92m\033[1mLoop of length',len(loop)-1,'found\033[0m \033[1mafter', time_elapsed(), 'seconds.\033[0m')
	for i in range(len(p1)):
		loop[i] = p1[i]
	for i in range(len(p2)):
		loop[-1-i] -= p2[i]
	report_loop(a,b,loop)

# Search for a pair of paths, with equal ends, for q=a/b,
# with all u/v satisfying |u/v| <= Ca/2, where C >= 2.
# Here u/v refers to the notation in the paper and denotes the fractions
# obtained by multiplying by a the endpoints of proper sub-paths of a given path.
# Here u,v are always positive integers, because we can alter their sign by multiplying the path terms by -1.
# If an appropriate pair is found, update database and return True.
def find_loop (a, b, C, max_paths, max_iter, max_visited = 0):
	global t1
	t1 = datetime.datetime.now()
	print (datetime.datetime.now().strftime('%H:%M:%S,'), 'considering q =', str(a)+'/'+str(b) + ', C =', str(C) + ', with up to', max_paths, 'paths,', max_iter, 'iterations.')
	paths = [] # The set of paths in a current iteration (all of the same length)
	# For each path we store:
	#  the value of the endpoint times a, as a pair: u, v,
	#  the path itself (encoded as an integer),
	#  the square of the weight.
	# For performance reasons we store flattened tuples (u,v,p,wn,wd) instead of ((u,v), p, (wn,wd))
	#
	# Set up path encoding
	base = C+1+(C%2)
	sig = base
	#
	visited = {} # Map: fraction -> path (encoded), weight^2.
	# The fraction is the endpoint times a, as a pair: numerator, denominator.
	# Initially we store the mapping 0 -> (zero loop).
	# At each iteration we store at most max_paths paths, with the endpoint in (0, 1/2].
	#
	# The first sequence element m0 is chosen as positive.
	# We do not need -m0, as we consider these paths as +-.
	keep_visited_paths = True
	for m0 in range (1, 1 + C//2):
		paths.append((m0*a,1,m0,1,1)) # In this case m0 == e.
	visited[(0,1)] = 0, (1,1) # We do not need to record (m0*a,1), because if we can get there, we can get to 0 as well, with the same weight.
	#
	display_frequency = 1
	while display_frequency * C * max_paths < 100000:
		display_frequency *= 10
	for it in range(1,max_iter+1):
		if it % display_frequency == 0:
			print ('q = ' + str(a) + '/' + str(b) + ', C = ' + str(C) + ', M = ' +str(M) + ', iteration', it, 'of', max_iter)
			print ('Keeping track of', len(visited),'points already visited,', len(paths), 'current paths.')
# 			print ('Free memory:',psutil.virtual_memory()[4])
		new_paths = []
		for u,v, p, wn, wd in paths:
			wwn = wn*u*u # The weight of the new path only depends on the previous endpoints.
			wwd = wd*v*v*a*b
			d = gcd(wwn,wwd)
			wwn //= d
			wwd //= d
			uu,vv = a*b*v,u
			d = gcd(uu,vv)
			uu //= d
			vv //= d
			# The smallest possible numerator after adding the next m will be computed as r.
			r = uu % (a*vv)
			if 2*r > a*vv:
				r = a*vv - r
				r_reversed = True
			else:
				r_reversed = False
			# What is the digit e that would lead to r?
			if r == 0:
				e = 0
			else:
				e = -1 if r_reversed else 1
			np = p + e*sig
			if r_reversed:
				np = -np
			if e == 0: # Top digit 0 would not be detectable
				np += base*sig
			if (r,vv) in visited: # Either we got a non-unit-weight loop (yes!) or we have another, equivalent way of getting where we were (expendable).
				if visited[(r,vv)][1] != (wwn, wwd): # A loop of non-unit weight found.
					report_pair (a,b,C,np,visited[(r,vv)][0])
					return True
				else: # Discard the path, by not adding its descendants to new_paths
					continue
			elif keep_visited_paths:
				visited[(r,vv)] = (np,(wwn, wwd))
				keep_visited_paths = (len(visited) != max_visited)
			# What are the possible values of the next m = m_i?
			# -Ca/2 <= m a + uu/vv <= Ca/2
			# We compute the range of m's and the digit for the initial one.
			# Digits generally increase by 1 when m is incremented, except possibly for one point where we 'skip' one digit.
			# If we got here, we already know that we cannot reach 0 immediately.
			if (2*uu) % (a*vv) != 0: # We cannot reach 1/2
				m_begin = -((C*a*vv + 2*uu)//(2*a*vv))
				m_end = m_begin + C
				m_skip = 1 + (-uu)//(a*vv)
				e = uu//(a*vv) + m_begin
			else: # uu/a vv = 1/2 + integer
				# The possible endpoints are symmetric around 0, so we only need the upper half.
				m_begin = (a*vv - 2*uu)//(2*a*vv) # The first endpoint will be 1/2.
				m_end = m_begin + (C+1)//2
				m_skip = m_begin
				e = 0 # Ok, we could start with 1 and avoid skipping, but it will still happen if we reverse digits.
			# Now we have the possible m's
			for m in range(m_begin, m_end):
				if m == m_skip:
					e += 1
				if m == 0:
					e += 1
					continue # We only look for proper loops.
				uuu = uu + m*a*vv
				np = p + e*sig
				if uuu < 0:
					uuu = - uuu
					np = -np
				new_paths.append((uuu,vv, np, wwn, wwd))
				e += 1
		if not new_paths:
			print('No non-unit-weight loop found after', time_elapsed(), 'seconds.')
			return False
		# The new paths were already added to visited.
		# We also know that there are no repetitions of endpoints between them.
		paths = [] # We will only keep one path per endpoint.
		new_paths.sort()
		lastuv = 0,0
		for u,v, p, wn, wd in new_paths: # We get those with smaller numerators first
			if lastuv == (u,v):
				if (wn,wd) != (paths[-1][3], paths[-1][4]):
					report_pair(a,b,C,p,paths[-1][2])
			else:
				lastuv = (u,v)
				if len(paths) < max_paths:
					paths.append((u,v, p, wn, wd))
		sig *= base
	print('No non-unit-weight loop found after', time_elapsed(), 'seconds.')
	return False

fname = '04_parameters.csv'
fieldnames = ['a', 'b', 'C', 'M','length']
if not Path(fname).is_file():
	with open(fname, 'w', newline='') as file:
		writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
		writer.writeheader()


# First, the method was applied to q's with b <= 50 with various parameters.

Cs = [2,3]
while Cs[-1] < 221:
	Cs.append((Cs[-1]*7)//5)
parameters = []
for C in Cs:
	M = C
	while M <= 221:
		parameters.append((M,C))
		M = (M*5)//2

for M,C in sorted(parameters):
	if (M == 221 and b > 37): # The point when this approach was taking too much time without more results.
		continue
	for a,b in sorted(db_requests):
		find_loop (a,b,C,(M*C)//2,((a+b)*a)//b) # We take this opportunity to handle all 'requests' i.e. exceptions, allowing more than M paths, i.e. we try harder for these.
	db_save()
	for b in range(2, 51):
		for a in range(4*b-1,1,-1): # a = 4b-1, 4b-2, ..., 2
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				if find_loop (a,b,C,M,min(((a+b)*a)//b,1000000//M)):
					with open(fname, 'a', newline='') as file:
						writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
						writer.writerow({'a':a,'b':b,'C':C,'M':M,'length':db_rows[(a,b)]['length']})
		db_save()

# On the basis of results for b <= 50 we determined pairs of parameters
# appropriate for initial 'sieving'.
# The idea is to treat the majority of cases with fairly light parameters, so results can be obtained quickly.
# Unfortunately, we cannot predict which q's can be handled with light parameters, so we tried them all.

Cs = [2,3]
while Cs[-1] < 36:
	Cs.append((Cs[-1]*7)//5)
parameters = []
for C in Cs:
	M = C
	while M < 20*C:
		parameters.append((M,C))
		M = (M*5)//2

for M,C in sorted(parameters):
	if M <= 16:
		BB = B # B == 300 is the maximum range of b's we consider. But after M == 16 we had to limit the range to 200.
	else:
		BB = 200 # Computations were taking too long.
	if M > 137 and M not in [342, 655]:
		continue # It turned out that differences between parameters were too small to make a significant difference. Therefore we had to skip some parameter sets.
	for b in range(2, BB+1):
		if (M,C,b) <= (0,0,0): # This line can be modified accordingly if calculations were interrupted and are to resume.
			continue
		with open(Path(__file__).stem + '_current.txt', 'w', newline='') as file:
			file.write('M = ' + str(M) + ', C = ' + str(C) + ', b = ' + str(b) + '\n')
		for a in range(4*b-1,1,-1): # a = 4b-1, 4b-2, ..., 2
			if (M > 2 or b > 241) and 2*a > 5*b: # We have given up trying for a/b > 5/2.
				continue
			if (M == 655) and (b > 150) and (3*a > 4*b):
				continue
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				if find_loop (a,b,C,M,min(((a+b)*a)//b,1000000//M)):
					with open(fname, 'a', newline='') as file:
						writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
						writer.writerow({'a':a,'b':b,'C':C,'M':M,'length':db_rows[(a,b)]['length']})
		db_save()
		with open(Path(__file__).stem + '_current.txt', 'a', newline='') as file:
			file.write('Done.\n')


# We can try to get possibly shortest loops
# for the initial entries.
# This version of find_loop() is not optimised for finding shortest loops.
# If it finds two matching paths of length <= max_iter, it will be happy
# to join them and make a loop of greater length.
# However, we still succeed in finding loops of decent length.

a,b,target_length,max_length = 11,3,14,14
for C in range(4*a):
	for M in range(C,a*a*C):
		if db_worth_considering (a, b, target_length):
			if find_loop (a,b,C,M,max_length):
				db_save()

a,b,target_length,max_length = 15,4,16,16
C = 1
M = 1000
while db_worth_considering (a, b, target_length) and M > 1:
	if find_loop (a,b,C,M,max_length):
		db_save()
	else:
		C = (1+C*3)//2
		M = (M*2)//3

for b in range(2, 71):
	for a in range((5*b)//2,1,-1):
		if db_in_scope(a,b) and not db_entry_exists(a,b):
			with open(Path(__file__).stem + '_current.txt', 'a', newline='') as file:
				file.write('q = ' + str(a) + '/' + str(b))
			C = ((a+b)*a)//b
			if find_loop (a,b,C,2*C,3*C):
				with open(Path(__file__).stem + '_current.txt', 'a', newline='') as file:
					file.write('Success!')
			else:
				with open(Path(__file__).stem + '_current.txt', 'a', newline='') as file:
					file.write('-')
	db_save()

# For b > 70 we will not try q > 20/9. When we fail for some q below that limit, we will lower the limit.
# We start from lower a to higher now, because then we limit the range faster,
# which is a better performance gain than propagating results to divisors.
limit = (20,9)
for b in range(71, B+1):
	for a in range(1+(5*b)//2): # The actual range will be shorter.
		if (b > 70) and (limit[1]*a > limit[0]*b):
			continue
		# To perform some computations in parallel on 11 machines we can
		# change one of the following eleven "pass" statements to "continue", a different one on each machine.
		if b in [101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]: # Prime denominators are hardest.
			pass
		if b not in [101, 103, 107, 109, 113]:
			pass
		if b not in [127, 131, 137, 139]:
			pass
		if b not in [149, 151, 157]:
			pass
		if b not in [163, 179]:
			pass
		if b not in [167, 173]:
			pass
		if b not in [181]:
			pass
		if b not in [191]:
			pass
		if b not in [193]:
			pass
		if b not in [197]:
			pass
		if b not in [199]:
			pass
		if db_in_scope(a,b) and not db_entry_exists(a,b):
			with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
				file.write('q = ' + str(a) + '/' + str(b) + ', C = ' + str(C) + ', M = ' +str(M) + ' ')
			C = ((a+b)*a)//b
			if find_loop (a,b,C,2*C,3*C):
				db_save()
				with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
					file.write('Success!\n')
			else:
				with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
					file.write('-\n')
				limit = (a,b)

# We would really like to find a solution for 39/10.

(a,b) = (39,10)
C = 200
while C < 10000:
	M = C
	while M < 10000:
		if db_in_scope(a,b) and not db_entry_exists(a,b):
			if find_loop (a,b,C,M,300,5000000):
				db_save()
		M *= 2
	C = (3*C)//2

# There are only 12 remaining unhandled q's with b <= 100, q < 2. All have b = 97.
obstacles = [(177, 97), (179, 97), (181, 97), (182, 97), (183, 97), (184, 97), (187, 97), (188, 97), (189, 97), (190, 97), (191, 97), (193, 97)]
C = 200
while C < 10000:
	M = C
	while M < 10000:
		for (a,b) in obstacles:
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				if find_loop (a,b,C,M,300,5000000):
					db_save()
		M *= 2
	C = (3*C)//2

# There are only 6 remaining unhandled q's with b <= 150, q < 3/2. All have b = 149.
obstacles = [(214, 149), (216, 149), (218, 149), (219, 149), (220, 149), (223, 149)]
C = 200
while C < 10000:
	M = C
	while M < 10000:
		for (a,b) in obstacles:
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				if find_loop (a,b,C,M,300,5000000):
					db_save()
		M *= 2
	C = (3*C)//2

# There are 102 remaining unhandled q's with b <= 300, q < 1.
obstacles = [(262, 283), (263, 283), (264, 283), (265, 283), (266, 283), (267, 283), (268, 283), (269, 283), (270, 283), (271, 283), (272, 283), (273, 283), (274, 283), (275, 283), (276, 283), (277, 283), (278, 283), (279, 283), (280, 283), (281, 283), (282, 287), (284, 287), (269, 289), (271, 289), (274, 289), (275, 289), (276, 289), (277, 289), (278, 289), (281, 289), (282, 289), (283, 289), (284, 289), (285, 289), (286, 289), (287, 289), (274, 291), (281, 291), (283, 291), (284, 291), (286, 291), (287, 291), (289, 291), (263, 293), (264, 293), (265, 293), (266, 293), (267, 293), (268, 293), (269, 293), (270, 293), (271, 293), (272, 293), (273, 293), (274, 293), (275, 293), (276, 293), (277, 293), (278, 293), (279, 293), (281, 293), (282, 293), (283, 293), (284, 293), (285, 293), (286, 293), (287, 293), (288, 293), (289, 293), (290, 293), (291, 293), (272, 295), (277, 295), (279, 295), (289, 295), (293, 295), (269, 298), (271, 298), (273, 298), (275, 298), (277, 298), (279, 298), (283, 298), (285, 298), (289, 298), (291, 298), (293, 298), (295, 298), (270, 299), (274, 299), (278, 299), (280, 299), (284, 299), (285, 299), (287, 299), (288, 299), (291, 299), (292, 299), (293, 299), (295, 299), (296, 299), (297, 299)]
C = 200
while C < 10000:
	M = C
	while M < 10000:
		for (a,b) in obstacles:
# One pair of parameters was not used, because of lack of memory:
			if (C,M) == (7683, 7683):
				continue			
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
					file.write('q = ' + str(a) + '/' + str(b) + ', C = ' + str(C) + ', M = ' +str(M) + ' ')
				if find_loop (a,b,C,M,300,5000000):
					db_save()
					with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
						file.write(' Success!\n')
				else:
					with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
						file.write(' -\n')
		M *= 2
	C = (3*C)//2

# We try again with more iterations, but smaller dictionary
obstacles = [(281, 293), (283, 293)]

C = 200
while C < 10000:
	M = C
	while M < 10000:
		for (a,b) in obstacles:
			if db_in_scope(a,b) and not db_entry_exists(a,b):
				with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
					file.write('q = ' + str(a) + '/' + str(b) + ', C = ' + str(C) + ', M = ' +str(M) + ' ')
				if find_loop (a,b,C,M,1000,1000000):
					db_save()
					with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
						file.write(' Success!\n')
				else:
					with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
						file.write(' -\n')
		M *= 2
	C = (3*C)//2

(a,b) = (39,10) # Again!

Cs = [((a+b)*a)//b]
for i in range(6):
	Cs.append(Cs[-1]*2)
for C in Cs:
	M = 200000 # This seems to be the limit if we have 48 GB of RAM available for computations.
	if db_in_scope(a,b) and not db_entry_exists(a,b):
		with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
			file.write('q = ' + str(a) + '/' + str(b) + ', C = ' + str(C) + ', M = ' +str(M) + ' ')
		if find_loop (a,b,C,M,300,5000000):
			db_save()
			with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
				file.write('Success!\n')
		else:
			with open(Path(__file__).stem + '_log.txt', 'a', newline='') as file:
				file.write('-\n')


exit()

# Below are some examples of minimal parameters where loops are found for particular qs.
# They show that such minimal parameters are pretty irregular.
# Moreover, finding a loop does not depend on the parameters chosen in a monotone way.
# We might succeed with fewer paths, and fail with more paths.

a,b = 73,29
find_loop (a,b,32,128,200)

a,b = 41,11
find_loop (a,b,2,6,1000)


a,b = 97,41
find_loop (a,b,33,429,1000)

a,b = 101,41
find_loop (a,b,8,16,1000)


a,b = 103,41
find_loop (a,b,37,37,1000)



a,b = 97,37
find_loop (a,b,36,180,1000)
find_loop (a,b,37,185,1000)
find_loop (a,b,34,340,1000)
find_loop (a,b,37,333,1000)

a,b = 101,37
find_loop (a,b,18,126,1000)

a,b = 103,37
find_loop (a,b,47,611,1000)

