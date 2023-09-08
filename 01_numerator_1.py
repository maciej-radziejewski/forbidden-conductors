# Find a loop of non-unit weight for a given q=a/b.
# As the first step we handle all q of the form 1/b.

# Results are saved in the database file loops.csv
# For each q = a/b we find one loop and store:
# a, b, example loop, its length, weight, and method (script number).

# In subsequent steps we search for loops in other cases,
# using other methods, and add the data to the same database.
# Only loops of non-unit weight are stored, one per each q.

from common import *
current_method = int(Path(__file__).stem.split('_')[0])

for b in range(2, B+1):
	a = 1
	if db_worth_considering(a,b,1):
		db_submit_entry (a, b, (1, -b), '\\sqrt{\\frac{' +str(a)+'}{' + str(b) + '}}', current_method)

db_save()

