# Find loops for q=a/b with a given a and all possible residue classes of b, -b mod a.

from common import *
current_method = int(Path(__file__).stem.split('_')[0])

done = {}
# modulus_for_exceptions = 1

def needed (a,b,M):
	global done
	r = b % a
	if a not in done:
		done[a] = {}
	if r not in done[a]:
		done[a][r] = []
	tab = done[a][r]
	for aa, bb, MM, p1, p2 in tab:
		if M % MM == 0 and ((b - bb) % MM == 0 or (b + bb) % MM == 0):
			return False
	return True

def report (instance):
	global done
	a, b, M, path1, path2 = instance
	r = b % a
	if a not in done:
		done[a] = {}
	if r not in done[a]:
		done[a][r] = []
	new_list = [instance]
	for old in done[a][r]:
		aa, bb, MM, p1, p2 = old
		if MM % M != 0 or ((b - bb) % M != 0 and (b + bb) % M != 0):
			new_list.append(old)
	done[a][r] = new_list

# Return the nth root of num/den if rational, 0/1 otherwise.
# num, den, n must be positive integers.
def rational_root (num, den, n):
	u = int(num**(1/n)) - 1
	while (u**n < num):
		u += 1
	v = int(den**(1/n)) - 1
	while (v**n < den):
		v += 1
	if u**n != num or v**n != den:
		return 0,1
	else:
		return u,v

def weight_square (a,b,m):
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
	wn = wn*wn
	wd = wd*wd*(a*b)**k
	d = gcd(wn,wd)
	wn //= d
	wd //= d
	return ((wn,wd))

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

# Given a path m for q=a/b, epsilon = 1 or -1,
# and given bb s.t. epsilon b \equiv b (mod N) for an appropriate N,
# return the path m' for q=a/bb
# s.t. the u/v visited will be the same up to sign.
def mod_path (m, a, b, bb, epsilon):
	if len(m) == 0:
		return []
	k = len(m)-1
	mm = m.copy()
	mm[0] = m[0]
	ej = 1 # epsilon[j] in the notation of the proposition.
	u = a*m[0]
	v = 1
	for j in range(k):
		mm[j+1]	= ej*epsilon*m[j+1] + ((ej*epsilon*b - ej*bb)//u) * v
		ej *= epsilon
		u,v = a*b*v,u
		d = gcd(u,v)
		u //= d
		v //= d
		u += a*v*m[j+1]
	return mm

def save():
	global done#, modulus_for_exceptions
	fname = 'paths_mod.csv'
	fieldnames = ['a', 'residue', 'modulus', 'exception', 'path1', 'path2']
	if not Path(fname).is_file():
		with open(fname, 'w', newline='') as file:
			writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
			writer.writeheader()
	with open(fname, 'a', newline='') as file:
		writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
		for a in done: # Really just one a.
# 			modulus_for_exceptions = a
			for r in done[a]:
				for a, b, M, p1, p2 in done[a][r]:
					# modulus_for_exceptions = lcm (modulus_for_exceptions, M)
					w1 = weight_square(a,b,p1)
					w2 = weight_square(a,b,p2)
					k = max(len(p1)-1, 0)
					l = max(len(p2)-1, 0)
					exc = 0
					if (k-l)%2 != 0:
						print('Unexpected entry:', a, b, M, p1, p2)
						exit()
					if k == l:
						if w1 == w2:
							print('Unexpected entry (equal lengths and weights):', a, b, M, p1, p2)
							exit()
					else:
						u = w1[0]*w2[1]
						v = w1[1]*w2[0]
						d = gcd (u,v)
						u //= d
						v //= d
						if k > l:
							uu,vv = rational_root(u,v,k-l)
						else:
							uu,vv = rational_root(v,u,l-k)
						if b%vv == 0: # The exception, if any, must be an integer.
							exc = uu*(b//vv) # If the root were not rational, we would get exc == 0 here.
						if (b-exc)%M != 0 and (b+exc)%M != 0: # The exception is not in our residue class anyway.
							exc = 0
					writer.writerow({'a':a, 'residue':b, 'modulus':M, 'exception':exc, 'path1':p1, 'path2':p2})
					if exc > 1 and 4*exc > a: # Of course, q=a/1 and q>4 define unique weights
						db_request_checking (a,exc)
					for bb in range(1 + a//4, B+1):
						if bb != exc and db_worth_considering (a, bb, k+l):
							epsilon = 0
							if (bb-b) % M == 0:
								epsilon = 1
							elif (bb+b) % M == 0:
								epsilon = -1
							if epsilon:
								np1 = mod_path (p1, a, b, bb, epsilon)
								np2 = mod_path (p2, a, b, bb, epsilon)
								loop = [0] * (k+l+1)
								if np1:
									for j in range(k+1):
										loop[j] += np1[j]
								if np2:
									for j in range(l+1):
										loop[k+l-j] -= np2[j]
								db_submit_entry (a, bb, loop, weight(a, bb, loop), current_method)
	done = {}

def factorisation(n):
	f = []
	p = 2
	while p <= n:
		if n % p == 0:
			k = 0
			while n % p == 0:
				n //= p
				k += 1
			f.append((p,k))
		p += 1
	return f

def divisors(n):
	div = [1]
	for p,k in factorisation(n):
		new_div = div.copy()
		for d in div:
			for j in range(k):
				d *= p
				new_div.append(d)
		div = new_div
	return sorted(div)

# Search for a pair of paths, with equal ends, for q=a/b with all u's dividing M.
# Here u’s refers to the notation in the paper and denotes the numerators of fractions u/v
# obtained by multiplying by a the endpoints of proper sub-paths of a given path.
# Here u,v are always positive integers, because we can alter their sign.
# For paths of different length we always get the assertion for all except at most one b.
# Checking paths of equal length is more complex, as it requires storing and comparing weights.
# If an appropriate pair is found, update the in-memory database and return True.
def loops_found(a, b, M):
	if not needed (a,b, M):
		return True
	paths = [] # The set of paths in a current iteration (all of the same length)
	# For each path we store:
	#  the modulus (the LCM of u’s)
	#  the path itself (as list of integers),
	#  the value of the endpoint times a, as a pair: u, v, and
	#  a value proportional to the weight (comparable for paths of equal length).
	#
	visited = {} # Map: fraction -> path, where we store the path and modulus only.
	# The fraction is the endpoint times a, as a pair: numerator, denominator.
	#
	div = divisors(M)
	#
	# The first sequence element must be m0 such that a*m0 divides M.
	for d in div:
		if d%a == 0:
			paths.append((d, [d//a],(d,1), (1,1))) # We do not need -d, as we consider these paths as +-.
			visited[(d,1)] = [d//a], d
	#
	found = [] # The list of path pairs found.
	while not found:
		new_paths = []
		for mod, p, (u,v), (wn, wd) in paths:
			nmod = lcm (mod, u)
			uu,vv = a*b*v,u
			d = gcd(uu,vv)
			uu //= d
			vv //= d
			wwn = wn*u
			wwd = wd*v
			d = gcd(wwn,wwd)
			wwn //= d
			wwd //= d
			if vv == 1 and uu % a == 0: # Loop found!
				found.append((a, b, nmod, p + [-(uu//a)], [0]))
			for d in div:
				if (d-uu) % (a*vv) == 0:
					m = (d-uu) // (a*vv)
					np = p + [m]
					if (d,vv) in visited:
						found.append((a, b, lcm(nmod, visited[(d,vv)][1]), np, visited[(d,vv)][0]))
					new_paths.append((nmod, np, (d,vv), (wwn, wwd)))
				if (-d-uu) % (a*vv) == 0:
					m = (-d-uu) // (a*vv)
					# Store negatives, because we store d/vv instead of -d/vv.
					np = [-p[i] for i in range(len(p))] 
					np.append(-m)
					if (d,vv) in visited:
						found.append((a, b, lcm(nmod, visited[(d,vv)][1]), np, visited[(d,vv)][0]))
					new_paths.append((nmod, np, (d,vv), (wwn, wwd)))
		if not new_paths:
			return False
		# Now we need to find relations among the current paths: same fraction, different weight.
		# Along the way we add them to visited, keeping the one with the smaller modulus.
		# (All moduli divide M, but this is an extra optimization to keep the smaller ones).
		# If found is empty, then the current fractions are not yet in visited.
		# Otherwise we can set visited to empty, as it will not be needed later.
		# This way, if we find the fraction in visited, it must have been added in this loop,
		# so it is also in weights.
		if found:
			visited = {}
		weights = {} # Map: fraction -> weight
		paths = [] # We will only keep one path per endpoint.
		for mod, p, (u,v), (wn, wd) in sorted(new_paths): # We get those with smaller moduli first
			if (u,v) not in visited:
				visited[(u,v)] = (p, mod)
				weights[(u,v)] = (wn, wd)
				paths.append((mod, p, (u,v), (wn, wd)))
			else:
				if weights[(u,v)] != (wn, wd): 
					found.append ((a, b, lcm(mod, visited[(u,v)][1]), visited[(u,v)][0], p))
	solution = min(found)
	report(solution)
	M = [solution[0]]
	for f in found:
		i = 0
		while i < len(M) and f[0] % M[i] != 0:
			i += 1
		if i == len(M):
			report (f)
			M.append(f[0])
	return True



# Returns the LCM of positive integers < n.
def pprod(n):
	M = 1
	for k in range(2,n):
		M = lcm(M,k)
	return M

# The following works for a >= 3,
# because we need iteration_end < a.
def numerator(a):
	# We have a complex iteration over residue classes of b
	# mod na for various n, branching when necessary.
	# The following means: b = 0 (mod 1), b = 1 (mod a*n), where n = LCM(2,...,(a-1)//2)
	iter = [0, 1, 1, lcm(a,pprod((a+1)//2))]
	iteration_end = iter[3]//2 + 1
	while iter[2] != iteration_end:
		b = iter[-2]
		if gcd(a,b) == 1:
			print (datetime.datetime.now().strftime('%H:%M:%S, ') + 'a = '+str(a) + ', b = ' + ', '.join([str(iter[2*i]) + ' (mod ' + str(iter[2*i+1]) + ')' for i in range(1,len(iter)//2)]))
		if gcd(a,b) > 1 or loops_found(a, b, iter[-1]):
			iter[-2] += iter[-3]
			while iter[-2] == iter[-4] + iter[-1]: # Have we considered all sub-cases created by branching?
				# This only ever happens if len(iter) >= 6.
				iter.pop()
				iter.pop()
				iter[-2] += iter[-3] # Advance to the next residue for the previous modulus.
		else: # We have to decide: either branch or drop the current modulus and try the next one.
			progress = (iter[-2] - iter[-4]) // iter[-3]
			if len(iter) == 4 or progress*progress*progress*iter[3] >= iter[-1]: # We wish to keep the results for previos residues mod iter[-1]
				iter.append(iter[-2]) # We branch to the same b
				iter.append(2*iter[-2]) # mod multiples of the current modulus.
			else:
				iter[-1] += iter[-3] # Try the next multiple of the previous modulus.
				iter[-2] = iter[-4] # Have to reset the residue.		

# A variant of loops_found, for handling exceptions
def loops_found_nonunit(a, b, M):
	print(datetime.datetime.now().strftime('%H:%M:%S, ') + 'Checking', str(a)+'/'+str(b),'mod',M)
	paths = [] # The set of paths in a current iteration (all of the same length)
	visited = {} # Map: fraction -> path, where we store the path and modulus only.
	div = divisors(M)
	for d in div:
		if d%a == 0:
			paths.append((d, [d//a],(d,1), (1,1))) # We do not need -d, as we consider these paths as +-.
			visited[(d,1)] = [d//a], d
	found = [] # The list of path pairs found.
	while True: # We return from inside the loop.
		new_paths = []
		for mod, p, (u,v), (wn, wd) in paths:
			nmod = lcm (mod, u)
			uu,vv = a*b*v,u
			d = gcd(uu,vv)
			uu //= d
			vv //= d
			wwn = wn*u
			wwd = wd*v
			d = gcd(wwn,wwd)
			wwn //= d
			wwd //= d
			if vv == 1 and uu % a == 0: # Loop found!
				found.append((a, b, nmod, p + [-(uu//a)], [0]))
			for d in div:
				if (d-uu) % (a*vv) == 0:
					m = (d-uu) // (a*vv)
					np = p + [m]
					if (d,vv) in visited:
						found.append((a, b, lcm(nmod, visited[(d,vv)][1]), np, visited[(d,vv)][0]))
					new_paths.append((nmod, np, (d,vv), (wwn, wwd)))
				if (-d-uu) % (a*vv) == 0:
					m = (-d-uu) // (a*vv)
					# Store negatives, because we store d/vv instead of -d/vv.
					np = [-p[i] for i in range(len(p))] 
					np.append(-m)
					if (d,vv) in visited:
						found.append((a, b, lcm(nmod, visited[(d,vv)][1]), np, visited[(d,vv)][0]))
					new_paths.append((nmod, np, (d,vv), (wwn, wwd)))
		if not new_paths:
			return False
		# Check the pairs found to see if any of them have non-equal weights.
		for a, b, M, p1, p2 in found:
			w1 = weight_square(a,b,p1)
			w2 = weight_square(a,b,p2)
			if w1 != w2:
				k = max(len(p1)-1, 0)
				l = max(len(p2)-1, 0)
				loop = [0] * (k+l+1)
				if p1:
					for j in range(k+1):
						loop[j] += p1[j]
				if p2:
					for j in range(l+1):
						loop[k+l-j] -= p2[j]
				db_submit_entry (a, b, loop, weight(a, b, loop), current_method)
				return True
		found = []
		# Now we need to find relations among the current paths: same fraction, different weight.
		# Along the way we add them to visited, keeping the one with the smaller modulus.
		# If some endpoint is already in visited, and we did not return True above,
		# then necessarily all current paths with this endpoint have the same weight as the one in visited,
		# so we discard them.
		weights = {} # Map: fraction -> weight
		paths = [] # We will only keep one path per endpoint.
		for mod, p, (u,v), (wn, wd) in sorted(new_paths): # We get those with smaller moduli first
			if (u,v) not in visited:
				visited[(u,v)] = (p, mod)
				weights[(u,v)] = (wn, wd)
				paths.append((mod, p, (u,v), (wn, wd)))
			elif (u,v) in weights: # The endpoint (u,v) was added to visited in this loop.
				if weights[(u,v)] != (wn, wd): 
					found.append ((a, b, lcm(mod, visited[(u,v)][1]), visited[(u,v)][0], p))
		# Go through "found" again. Same loop as before. The w1 != w2 check is redundant now.
		for a, b, M, p1, p2 in found:
			w1 = weight_square(a,b,p1)
			w2 = weight_square(a,b,p2)
			if w1 != w2:
				k = max(len(p1)-1, 0)
				l = max(len(p2)-1, 0)
				loop = [0] * (k+l+1)
				if p1:
					for j in range(k+1):
						loop[j] += p1[j]
				if p2:
					for j in range(l+1):
						loop[k+l-j] -= p2[j]
				db_submit_entry (a, b, loop, weight(a, b, loop), current_method)
				return True
		found = []
		if not paths:
			return False


def handle_exceptions(a):
	for (aa,b) in sorted(db_requests):
		if aa == a:
			M = lcm(a,pprod((a+1)//2))
			k = 1
			max_k = 1000
			while k < max_k and not loops_found_nonunit (a,b,k*M):
				k += 1
			if k == max_k:
				print('Exception', str(a)+'/'+str(b),'noted, to be checked again at a later stage.')


for a in range(3,25):
	numerator(a)
	save()
	db_save()
	handle_exceptions(a)
	db_save()

