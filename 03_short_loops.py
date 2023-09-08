# Find a loop of non-unit weight for a given q=a/b.
# As the third step we look for all possible short loops
# for q=a/b with a > 3.

# Results are saved in the database file loops.csv
# For each q = a/b we find one loop and store:
# a, b, example loop, its length, weight, and method (script number).

# In subsequent steps we search for loops in other cases,
# using other methods, and add the data to the same database.
# Only loops of non-unit weight are stored, one per each q.

# This file was slightly revised before the paper was published,
# but after it was made available on arXiv. The reason for revision
# was a problem found in the original version of the code.
# The problem was such that it could not produce false loops, but a false proof
# of non-existence of loops of a given length, leading potentially to a false
# claim that another loop, of greater length, is shortest possible.
# This bit of extra information was included in the online tables only.
# In order to rule out the possibility of such false claims,
# the corresponding part of calculations was repeated, and new results
# were found identical to the originally reported ones. 
# In addition, the performance of the code was improved.
# Details are described below.
# 
# It is possible that, in the function solve_min_recursive,
# the polynomial considered could have a single term with maximum degree
# among all terms, however not containing all of the remaining variables.
# In that case it might not be valid to state that at least one of the variables
# must be small (below the bound computed), hence the code could miss some
# of the solutions. As a result, some results in the table might be incorrectly 
# claimed to be optimal. The problem was fixed in the new version of the code. 
# 
# Moreover, the following performance problem was addressed.
# We look for integer solutions of equations of the form
# (ax + b)(a'y + c) = d
# by iterating over the possible values of x, to find solutions with
# the first factor small, and then over y, to find the other solutions,
# with the second factor being small.
# The problem was that the criterion for 'small' was the same for both factors, 
# even when |a| and |a'| differed greatly.
# In the present version the bounds are such that the number of iterations for both
# factors is roughly the same. In addition, the equation is first solved mod a and
# mod a', when the number of iterations is sufficient to make this worthwhile.
# Further optimization is naturally possible, by employing advanced non-trivial
# factorization techniques, but it would require a deeper analysis
# (with billions of 'easy' cases such an optimization might actually slow us down).
# 
# Another small modification was in the file 'common.py',
# where isqrt is now imported instead of sqrt.
# Moreover, the in_scope() function was corrected to include the cases actually covered.



from common import *

N = 6

current_method = int(Path(__file__).stem.split('_')[0])
undisplayed_depth = 5 # for displaying the values of ms.

def propagate_loop_mod (a, b, loop, k, weight):
	# Propagate results from q=a/b to other q=a/b',
	# for b' satisfying appropriate congruence conditions.
	# The k here is half of the k from the paper.
	# We can assume eps[0] == 1, because if signs of all epsilon are 
	# reversed, we get a negative of the new loop, so same weight.
	hval = [evaluate (h[j], loop, a, b) for j in range(k+1)]
	gval = [evaluate (g[j], loop, a, b) for j in range(k+1)]
	u = [0 for j in range(2*k)]
	v = [0 for j in range(2*k)]
	for j in range(0,k):
		num,den = a*hval[j][0]*gval[j][1],gval[j][0]*hval[j][1]
		d = gcd(num,den)
		u[2*j] = num//d
		v[2*j] = den//d
	for j in range(0,k):
		num,den = b*gval[j+1][0]*hval[j][1],hval[j][0]*gval[j+1][1]
		d = gcd(num,den)
		u[2*j+1] = num//d
		v[2*j+1] = den//d		
	for bb in range (a//4+1, B+1):
		if not db_worth_considering (a, b, 2*k):
			continue
		eps = [1 for j in range(2*k+1)]
		congruence_failed = False
		for j in range(2*k):
			if (bb-b)%u[j] == 0:
				eps[j+1] = eps[j]
			elif (bb+b)%u[j] == 0:
				eps[j+1] = -eps[j]
			else:
				congruence_failed = True
				continue
		if congruence_failed:
			continue
		num,den = weight
		num *= b**k
		den *= bb**k
		if num == den:
			continue
		d = gcd(num,den)
		new_loop = [eps[j]*loop[j] for j in range(2*k+1)]
		for j in range(2*k):
			new_loop[j+1] += ((eps[j+1]*b - eps[j]*bb)//u[j])*v[j]
		db_submit_entry (a, bb, new_loop, (num//d, den//d), current_method)

# For testing.
# def divisors (a,b):
# 	div_a = set()
# 	d = 1
# 	while d*d <= a:
# 		if a % d == 0:
# 			div_a.add (d)
# 			div_a.add (a//d)
# 		d += 1
# 	div_a -= {a}
# 	for d1 in div_a:
# 		for dd1 in div_a:
# 			if d1 % dd1 == 0:
# 				for d2 in range (1,1+200//b):
# 					for d3 in range (1,1+200//(b*d2)):
# 						aa = a//d1
# 						bb = b*d2*d3
# 						print(aa,bb)

def report_loop (a, b, loop, k, weight):
	# Propagate results from q=a/b to other q,
	# using two propositions in the paper.
	# We first propagate to q/n and then shift the denominator
	# as this _might_ give more results.
	# We find all positive integers r, r' such that q/rr' is in our range.
	# We have r*r' = d1*d for some d1|a and d such that d*b <= B.
	# Therefore r = dd1*d3 and r' = (d1//dd1) * d2 for some dd1|d1 and d2*d3 == d.
	div_a = set()
	d = 1
	while d*d <= a:
		if a % d == 0:
			div_a.add (d)
			div_a.add (a//d)
		d += 1
	div_a -= {a}
	for d1 in div_a:
		for dd1 in div_a:
			if d1 % dd1 == 0:
				for d2 in range (1,1+B//b):
					for d3 in range (1,1+B//(b*d2)):
						aa = a//d1
						bb = b*d2*d3
						new_loop = loop.copy()
						for j in range (k):
							new_loop[2*j+1] *= (d1*d2//dd1)
						for j in range (k+1):
							new_loop[2*j] *= (dd1*d3)
						propagate_loop_mod (aa, bb, new_loop, k, weight)

# Sometimes we may arrive at a sub-case
# that cannot be solved using the methods implemented.
# This happens, for example, for q=11/5 and length 8.
# Then we record the equations left to solve in a text file.
# The encoding of equations is technical and meant only
# for the use by the author of the script.
# When such possibly infinite families of solutions are found,
# we cannot claim that we found a loop,
# nor can we claim that there are none.
def db_record_infinite (a, b, length, sols, excs):
	with open('infinite_families.txt', 'a', newline='') as file:
		file.write('q = ' + str(a)+'/'+str(b)+', length = '+str(length)+'\n')
		for s in sols:
			if None in s:
				file.write (str({}) + '\t' + str(subs) + '\n')
		for (poly, subs, ranges) in excs:
			file.write (str(poly) + '\t' + str(subs) + '\n')
		file.write('\n')
		

def db_record_unit_loops_only (a, b, length):
	entry = {'a': a, 'b': b, 'length': length}
	fieldnames = list(entry.keys())
	filename = 'unit_loops_only.csv'
	if not Path(filename).is_file():
		with open(filename, 'w', newline='') as file:
			writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
			writer.writeheader()
	with open(filename, 'a', newline='') as file:
		writer = csv.DictWriter(file, fieldnames=fieldnames, dialect=excel_semicolon)
		writer.writerow(entry)



# Given a polynomial f = \sum f[i]X^i of degree n
# s.t. the last coefficient is negative and the others non-negative
# find the smallest integer m s.t. f(m) < 0.
# Note that X^{-n} f is non-increasing and tends to f[n].
#
def get_min_bound (f):
	m = 0
	s = 0
	while s >=0:
		m += 1
		s = 0
		prod = 1
		for coeff in f:
			s += coeff*prod
			prod *= m
	return m

# When there is no polynomial left to solve,
# we just check if all variables have an assigned value.
# We return a solution or an exception, accordingly.
#
def solution_or_exception (M, substitutions, ranges_done):
	if len (substitutions) == M+1:
		solution = [None for i in range (M+1)]
		for (i,v) in substitutions.items():
			solution[i] = v
		return [solution], [] # One solution, no exceptions
	else:
		return [], [({}, substitutions.copy(), ranges_done.copy())] # This is really an exception, as it is an infinite family of solutions.

# A special case of the above, when there is one extra assignment left, so we avoid making a new copy of substitutions.
#
def solution_or_exception_extra (M, substitutions, ranges_done, ii, mii):
	if len (substitutions) == M:
		solution = [None for i in range (M+1)]
		for (i,v) in substitutions.items():
			solution[i] = v
		solution[ii] = mii
		return [solution], [] # One solution, no exceptions
	else:
		subs = substitutions.copy()
		subs[ii] = mii
		return [], [({}, subs, ranges_done.copy())] # This is really an exception, as it is an infinite family of solutions.

def get_range (a, b, c):
	# return the range of integers x satisfying |ax+b| <= c, possibly empty, e.g., if c < 0.
	if a < 0:
		a,b = -a,-b
	return range (-((c+b)//a), (c-b)//a + 1)


# Solve a quadratic equation
# a mx my + b mx + c my + d = 0,
# where a is guaranteed to be non-zero.
def solution_or_exception_quadratic (x, y, a, b, c, d, M, substitutions, ranges_done):
	sols = []
	ax = a
	ay = a
	det = a*d - b*c # We solve (ax mx + c)(ay my + b) = -det
	if det != 0:
		cd = gcd (ax, c)
		if cd > 1:
			ax //= cd
			c //= cd
			det //= cd
		cd = gcd (ay, b)
		if cd > 1:
			ay //= cd
			b //= cd
			if det % cd != 0:
				return [], [] # No solutions.
			det //= cd
		multx = 1 # Default values for variable substitution.
		multy = 1
		shiftx = 0
		shifty = 0
		if ax == ay: # We know that ax and ay have equal signs.
			if abs(ax) > 1 and (b*c + det) % ax:
				return [], [] # No solutions.
		else: # Hence max(|ax|, |ay|) >= 2
# 			if abs(det) > 300000000:
			if abs(det//(ax*ay)) > 70:
				axycd = gcd (ax, ay)
				axr = ax // axycd
				ayr = ay // axycd
				axrinv = pow (axr, -1, ayr)
				ayrinv = pow (ayr, -1, axr)
				# Our equation implies
				# c (ay my + b) ≡ -det (mod ax), so
				# ay my + b ≡ -det * cinv (mod ax),
				# where cinv is the inverse of c mod ax.
				if (det + b*c) % axycd:
					return [], [] # No solutions.
				# So b + det cinv ≡ 0 (mod axycd), hence
				# ay//axycd my ≡ (-b - det cinv)//axycd (mod ax//axycd)
				# ayr my ≡ (-b - det cinv)//axycd (mod axr),
				# my ≡ ((-b - det cinv)//axycd) ayrinv (mod axr),
				# where ayrinv is the inverse of ayr mod axr.
				# We get
				# my = my' axr + ((-b - det cinv)//axycd) ayrinv
				# and our equation becomes
				# (ax mx + c)(ay axr my' + b + ay ayrinv ((-b - det cinv)//axycd)) = -det
				cinv = pow (c, -1, ax)
				multy = axr
				shifty = ((-b - det * cinv)//axycd) * ayrinv
				# Each solution my will have to be replaced with multy my + shifty.
				b += ay * ayrinv * ((-b - det * cinv)//axycd)
				# The same reasoning applies mod ay. The equation implies, for new b,
				# (ax mx + c) b ≡ -det (mod ay axr),
				# and we have |ay axr| = |ax ayr|.
				if (det + b*c) % ax:
					return [], [] # No solutions.
				# ax mx b ≡ -b c - det (mod ax ayr),
				# mx b ≡ (-b c - det)//ax (mod ayr),
				binv = pow (b, -1, ayr)
				# mx ≡ ((-b c - det)//ax) binv (mod ayr),
				# mx = mx' ayr + ((-b c - det)//ax) binv
				# and our equation becomes
				# (ax ayr mx' + (-b c - det) binv + c)(ay my + b) = -det
				multx = ayr
				shiftx = ((-b * c - det)//ax) * binv
				c += (-b * c - det) * binv
				ax *= ayr
				ay *= axr
				cd = gcd (ax, c)
				if cd > 1:
					ax //= cd
					c //= cd
					if det % cd != 0:
						return [], [] # No solutions.
					det //= cd
				cd = gcd (ay, b)
				if cd > 1:
					ay //= cd
					b //= cd
					if det % cd != 0:
						return [], [] # No solutions.
					det //= cd
		r1 = isqrt(abs(det*ax)//abs(ay))
		r2 = abs(det)//(r1+1) # If |first factor| > r1, then |second factor| <= r2.
		for mx in get_range(ax, c, r1):
			factor = ax*mx + c
			if factor != 0 and det % factor == 0:
				cofactor = (-det // factor) - b
				if (cofactor != 0) and (cofactor % ay == 0):
					sols.append((mx, cofactor // ay))
		for my in get_range(ay, b, r2):
			factor = ay*my + b
			if factor != 0 and det % factor == 0:
				cofactor = (-det // factor) - c
				if (cofactor != 0) and (cofactor % ax == 0):
					sols.append((cofactor // ax, my))
		if len(substitutions) == M-1:
			solutions = []
			template = [None for i in range (M+1)]
			for (i,v) in substitutions.items():
				template[i] = v
			for mxx,myy in sols:
				mx = multx*mxx + shiftx
				my = multy*myy + shifty
				if abs(mx) >= ranges_done[x]:
					if abs(my) >= ranges_done[y]:
						solution = template.copy()
						solution[x] = mx
						solution[y] = my
						solutions.append(solution)
			return solutions, [] # No exceptions
	# Otherwise we only have exceptions.		
	exceptions = []
	if det == 0:
		if (c % ax == 0) and (c != 0):
			mx = -c//ax
			if abs(mx) >= ranges_done[x]:
				subs = substitutions.copy()
				subs[x] = mx
				exceptions.append(({}, subs, ranges_done.copy()))
		if (b % ay == 0) and (b != 0):
			my = -b//ay
			if abs(my) >= ranges_done[y]:
				subs = substitutions.copy()
				subs[y] = my
				exceptions.append(({}, subs, ranges_done.copy()))
	else:
		for mx, my in sols:
			if abs(mx) >= ranges_done[x]:
				if abs(my) >= ranges_done[y]:
					subs = substitutions.copy()
					subs[x] = mx
					subs[y] = my
					exceptions.append(({}, subs, ranges_done.copy()))
	return [], exceptions

def try_to_handle (M, terms, degrees, poly, substitutions, ranges_done):
	all_ms = set()
	for ms, coeff in poly.items():
		all_ms |= ms
	for i,v in substitutions.items():
		all_ms.add(i)
	if len(all_ms) < M+1: # Any solutions would have some of the ms arbitrary and that is not possible for a true loop.
		return [], []
	m_degree = degrees[0]
	sign = -1 if terms[0][1] < 0 else 1
	# We only handle one special case for now:
	if m_degree == 1 and terms[0][1] == sign and len(terms) == 3 and degrees.count(m_degree) == 2 and len(substitutions) == M-1:
		# Now mi = -sign * b * mj - c,
		# where terms[0][0] == {i}, terms[1][0] == j, c == terms[2][1],
		# so weight is abs of a quadratic polynomial in mj.
		# It is enough to check 5 values to know if it is always 1.
		# Maybe 6, because we need mi != 0.
		i = min(terms[0][0])
		j = min(terms[1][0])
		cc = -terms[2][1]
		bb = -sign * terms[1][1]
		solutions = []
		for mj in range(1,7):
			sol = [None for i in range (M+1)]
			for ii, mii in substitutions.items():
				sol[ii] = mii
			sol[j] = mj
			sol[i] = bb*mj + cc
			if sol[i] != 0:
				solutions.append(sol)
		return solutions, []
	else:
		# Multiply the equation by -1 if the major term had a negative coefficient.
		return [], [({k: v*sign for k, v in poly.items()}, substitutions.copy(), ranges_done.copy())]

# Solve a Diophantine equation in m_0, ..., m_M,
# by estimating minima.
# Return the list of solutions and the list of exceptions.
# poly must be a dictionary of frozenset() to int != 0,
# where each set stands for a product of distinct m_i's
# and maps to the coefficient.
#
# Each solution sol in the list is a list of m values, sol[i] = m_i.
# Each exception is a tuple: the polynomial (equated to 0), substitutions already made, ranges already checked.
#
def solve_min_recursive (M, poly, substitutions, ranges_done):
	global undisplayed_depth
	if not poly: # Zero polynomial
		return solution_or_exception (M, substitutions, ranges_done)
	terms = sorted(poly.items(), key = lambda item: -len(item[0]))
	degrees = [len(term[0]) for term in terms]
	m_degree = degrees[0] # == max(degrees), degree in m's
	if degrees.count(m_degree) > 1 or m_degree != M+1-len(substitutions): # We cannot use the minimum method.
		return try_to_handle (M, terms, degrees, poly, substitutions, ranges_done)
	if len(terms) == 1: # a non-zero monomial, but we only look for solutions in non-zero m's.
		return [], [] # No solutions, no exceptions.
	elif m_degree == 1: # a linear polynomial with a single term of degree 1 and at most one free term
		ii = min(terms[0][0]) # terms[0][0] is a singleton set
		coeff = terms[0][1]
		free = terms[1][1]
		if len(terms) != 2 or terms[0][0] != frozenset({ii}) or free % coeff != 0: # Just a double-check
			print('Unexpected polynomial: ' + mpoly_to_str(poly))
			exit()
		# In case m0 is the unknown, check if m0 > 0.
		mii = -free//coeff
		if abs(mii) < ranges_done[ii]:
			return [], [] # No solutions, no exceptions.
		else:
			return solution_or_exception_extra (M, substitutions, ranges_done, ii, mii)
	elif m_degree == 2:
		# an equation of the form: a mx my + b mx + c my + d = 0
		x = min(terms[0][0])
		y = max(terms[0][0])
		a, b, c, d = 0, 0, 0, 0
		problem = False
		for ms, coeff in terms:
			if ms == frozenset({x,y}):
				a = coeff
			elif ms == frozenset({x}):
				b = coeff
			elif ms == frozenset({y}):
				c = coeff
			elif ms == frozenset():
				d = coeff
			else: # There must be some extra linear term, so there are infinitely many solutions
				problem = True
		if a == 0 or problem:
			cd = -1 if terms[0][1] < 0 else 1 # Multiply the equation by -1 if the major term had a negative coefficient.
			return [], [({k: v//cd for k, v in poly.items()}, substitutions.copy(), ranges_done.copy())]
# 		if b*b+c*c > 10*abs(b*c):
		return solution_or_exception_quadratic (x, y, a, b, c, d, M, substitutions, ranges_done)
	diag = [0 for i in range(m_degree)]
	diag.append (-2*abs(terms[0][1]))
	for (ms, coeff) in terms:
		diag[len(ms)] += abs (coeff)
	bound = get_min_bound (diag)
	# There must be some i s.t. |m_i| < bound.
	ms_left = set()
	for (ms, coeff) in terms:
		ms_left = ms_left | ms
	solutions, exceptions = [], []
	ranges = ranges_done.copy()
	complexity = int (log(bound) * (len(ms_left)-1)**2)
	if len(ms_left) >= min(5, undisplayed_depth) or complexity > 30:
		print(datetime.datetime.now().strftime(' %H:%M:%S, ') + ', '.join(['m' + str(j) + '=' + str(substitutions[j]) for j in substitutions]) + '                     ', end='\r')
		undisplayed_depth = len(ms_left)
	subs = substitutions.copy()
	for i in ms_left:
		if ranges_done[i] < bound:
			for m in range(-bound+1,bound):
				if abs(m) < ranges_done[i]:
					continue
				subs[i] = m
				p = defaultdict(int)
				for (ms, coeff) in terms:
					if i in ms:
						p[ms - frozenset({i})] += coeff*m
					else:
						p[ms] += coeff
				cd = 0 # gcd of all coefficients of p
				cdnf = 0 # gcd of coefficients of non-free terms - must divide the free term, or there are no solutions.
				for (ms, coeff) in p.items():
					cd = gcd(cd, coeff)
					if ms:
						cdnf = gcd(cdnf, coeff)
				if cd == cdnf:
					sols, excs = solve_min_recursive (M, {k: v//cd for k, v in p.items() if v}, subs, ranges)
					solutions += sols
					exceptions += excs
			ranges[i] = bound
		subs.pop(i, None)
	return solutions, exceptions

def solve_min_recursive_outer (M, poly, substitutions, ranges_done):
	terms = sorted(poly.items(), key = lambda item: -len(item[0]))
	degrees = [len(term[0]) for term in terms]
	m_degree = degrees[0] # == max(degrees), degree in m's
	diag = [0 for i in range(m_degree)]
	diag.append (-2*abs(terms[0][1]))
	for (ms, coeff) in terms:
		diag[len(ms)] += abs (coeff)
	bound = get_min_bound (diag)
	# There must be some i s.t. |m_i| < bound.
	solutions, exceptions = [], []
	ranges = ranges_done.copy()
	subs = substitutions.copy()
	for i in range(1+(M//2)):
		for m in range(1,bound):
			subs[i] = m
			p = defaultdict(int)
			for (ms, coeff) in terms:
				if i in ms:
					p[ms - frozenset({i})] += coeff*m
				else:
					p[ms] += coeff
			cd = 0 # gcd of all coefficients of p
			cdnf = 0 # gcd of coefficients of non-free terms - must divide the free term, or there are no solutions.
			for (ms, coeff) in p.items():
				cd = gcd(cd, coeff)
				if ms:
					cdnf = gcd(cdnf, coeff)
			if cd == cdnf:
				sols, excs = solve_min_recursive (M, {k: v//cd for k, v in p.items() if v}, subs, ranges)
				solutions += sols
				exceptions += excs
		ranges[i] = bound
		subs.pop(i, None)
	return solutions, exceptions

def solve_min (mpoly):
	all_ms = set()
	for (ms, coeff) in mpoly.items():
		all_ms = all_ms | ms
	M = max(all_ms)
	# We look for non-zero solutions, so we treat the range (-1,1) as done.
	return solve_min_recursive_outer (M, {k: v for k, v in mpoly.items() if v}, {}, defaultdict(lambda: 1))

# Given a polynomial in ms and q, evaluate it for given m's and q=a/b.
# Return the value as numerator and denominator.
#
def evaluate (poly, ms, a, b):
	deg = max (poly) # poly is  dictionary, and max returns the greatest key, here the degree in q.
	s = 0
	for (qexponent, qterm) in poly.items():
		qfactor = a**qexponent * b**(deg-qexponent)
		for (mterm, coeff) in qterm.items():
			prod = qfactor*coeff
			for j in mterm:
				prod *= ms[j]
			s += prod
	cd = gcd (s, b**deg)
	return s//cd, b**deg//cd



g = [{0: {frozenset(): 1}}] # g[0] = q^0
h = [{0: {frozenset({0}): 1}}] # h[0] = m_0 q^0

for k in range(N):
	# g_{k+1} = m_{2k+1}q h_{k}+g_{k}
	g.append(defaultdict(lambda: defaultdict(lambda: 0)))
	for (qexponent, qterm) in g[k].items():
		for (mterm, coeff) in qterm.items():
			g[k+1][qexponent][mterm] = coeff
	for (qexponent, qterm) in h[k].items():
		for (mterm, coeff) in qterm.items():
			g[k+1][qexponent+1][mterm | frozenset({2*k+1})] = coeff
			# We are introducing a new variable, so there is no
			# repetition and we need not add coefficients.
	# h_{k+1} = m_{2k+2}g_{k+1}+h_{k}.
	h.append(defaultdict(lambda: defaultdict(lambda: 0)))
	for (qexponent, qterm) in h[k].items():
		for (mterm, coeff) in qterm.items():
			h[k+1][qexponent][mterm] = coeff
	for (qexponent, qterm) in g[k+1].items():
		for (mterm, coeff) in qterm.items():
			h[k+1][qexponent][mterm | frozenset({2*k+2})] = coeff

def encode_solution (magnitude, s):
	return tuple([magnitude]+[2*abs(s[i]) + (1 if s[i]*s[0] < 0 else 0) for i in range(len(s))])
# This peculiar encoding of solutions achieves two goals:
# a path m, its inverse, negative and negative of inverse are all mapped to one item,
# of these four we choose one of those with a positive leading term, lexicographically first.

def decode_solution (es):
	return [es[i]//2 if es[i] % 2 == 0 else -(es[i]//2) for i in range(1,len(es))]

# Find proper loops of length 2k for q=a/b.
# Actually we look for solutions to h_k = 0,
#
def find_loop (a,b,k):
	# Substitute q=a/b in b^k h[k].
	# All terms stay distinct, because q-degrees and m-degrees in h[k]
	# are related 1-1.
	with open(Path(__file__).stem + '_current.txt', 'w', newline='') as file:
		file.write('q = ' + str(a)+'/'+str(b)+', length = '+str(2*k))
	print ('q = ' + str(a)+'/'+str(b)+', length = '+str(2*k)+'                        ')
	mpoly = {}
	for (qexponent, qterm) in h[k].items():
		for (mterm, coeff) in qterm.items():
			mpoly[mterm] = coeff * a**qexponent * b**(k-qexponent)
	sols,excs = solve_min(mpoly)
	solset = set()
	for s in sols:
		magnitude = int(1000*sum([log(abs(s[i])) for i in range(2*k+1)]))
		solset.add(min(encode_solution(magnitude,s), encode_solution(magnitude,[s[2*k-i] for i in range(2*k+1)])))
	sols = []
	for es in sorted(solset): # Out of the many cases we want to present the simplest ones in the table. We put those with the smallest product first, and try to avoid negative ones.
		s = decode_solution(es)
		sols.append(s)
		sols.append([-s[2*k-i] for i in range(2*k+1)])
	loops_found = False
	non_unit_loops_found = False
	for s in sols:
		is_a_loop = True
		for j in range(1,k):
			num,den = evaluate (h[j], s, a, b)
			if num == 0:
				is_a_loop = False
		if is_a_loop:
			loops_found = True
			num,den = evaluate (g[k], s, a, b)
			if abs(num) != den:
				non_unit_loops_found = True
			report_loop (a, b, s, k, (abs(num),den))
	if non_unit_loops_found:
		pass
	elif len(excs) > 0:
		db_record_infinite (a, b, 2*k, sols, excs)
	else:
		db_record_lack_of_loops (a, b, 2*k)
		if loops_found:
			db_record_unit_loops_only (a, b, 2*k)
	if loops_found:
		db_save() # Even a loop of unit weight may have given loops of non-unit weight for other q.

def in_scope (a,b,k): # Finding all loops takes a long time when a/b is small and k is large, so we do not consider all cases.
	if k <= 2: # Length 2k = 2 or 4.
		return True
	if k == 3:
		return (b <= 28) or (b == 29 and a > b) or (b < 67 and 3*a > 4*b) or (b == 67 and a > 101)
	if k == 4:
		return (a > 3*b and b < 58) or (b == 58 and a > 175) or (b <= 4)
	if k == 5:
		return (b <= 5) or (a,b) == (39,10) or (a,b) == (23,6)
	if k == 6:
		return (b <= 4) or (a,b) == (39,10) or (a,b) == (23,6)
	return b <= 4 or (a,b) == (39,10)  # Need to change N to 7 to actually try k == 7.

for k in range(1, N+1): # Look for loops of length 2k
	for b in range(2, B+1): 
		for a in range(4*b-1,1,-1): # a = 4b-1, 4b-2, ..., 2
			if db_worth_considering (a,b,2*k) and in_scope (a,b,k):
				find_loop (a,b,k)

for a,b in sorted(db_requests):
	for k in range(1, N+1):
		if db_worth_considering (a,b,2*k) and (k <= 5 or b <= 5):
			find_loop (a,b,k)
