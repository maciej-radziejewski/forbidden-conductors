# What rational q remain in the range assumed?

from common import *

B = 300

count_all = 0
count_needed = 0
count_requested = len(db_requests)
min_q = (4,1) # The smallest unhandled q, initially set to 4/1
max_q = (0,1) # The largest handled q.
goals = {10: (4,1), 30: (3,1), 100: (2,1), 150: (3,2), 300: (1,1)} # Map bb -> qq, where we want to check all q = a/b < qq with b <= bb.
goal_blocking = {}

for b in range(2, B+1):
	min_decreased = False
	for a in range(1, 4*b):
		if db_in_scope(a,b):
			count_all += 1
			if not db_entry_exists (a,b):
				count_needed += 1
				if (a,b) in db_requests:
					count_requested -= 1
				if a*min_q[1]<b*min_q[0]:
					min_q = (a,b)
					min_decreased = True
				for bb in goals:
					if b <= bb and a*goals[bb][1] < b*goals[bb][0]:
						if bb not in goal_blocking:
							goal_blocking[bb] = []
						goal_blocking[bb].append((a,b))
			else:
				if a*max_q[1]>b*max_q[0]:
					max_q = (a,b)
	if min_decreased:
		min_decreased = False
		print ('For b \leq', b, ': q <', str(min_q[0])+'/'+str(min_q[1]), '=', min_q[0]/min_q[1], 'checked.')


print (count_all, 'q considered in total.')
print (count_all - count_needed, 'q already checked.')
print (count_needed, 'q to be checked, including', len(db_requests)-count_requested, 'exceptions.')
print (count_requested, 'exceptions to be checked in addition.')
print ('The largest handled q is', str(max_q[0])+'/'+str(max_q[1]), '=', max_q[0]/max_q[1], '.')

for bb in goals:
	if bb in goal_blocking:
		print('Obstacles for b <=', bb, ', q <', str(goals[bb][0])+'/'+str(goals[bb][1]) + ':')
		for (a,b) in goal_blocking[bb]:
			print(str(a)+'/'+str(b))
	else:
		print('No obstacles for b <=', bb, ', q <', str(goals[bb][0])+'/'+str(goals[bb][1]) + '.')
