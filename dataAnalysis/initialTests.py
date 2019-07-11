import pandas as pd 

# given the name of a portal, split the string up to find the name of the root
def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

# given a csv of (portal, eventname) pairs, process it into a dataframe of the correct shape
# named columns, and including the portal root as a column
def processFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['portal', 'eventname']
	result['proot'] = result.apply(lambda row: getPortalRoot(row['portal']), axis=1)
	return result

# takes in a row and determines if it's correct from the database of known results
# correct is if it's already present
# incorrect is if it's not present but the (portal, eventname) combo is present
# otherwise, unknown
def rowCorrectness( in_row, kc):
	if  kc.loc[(kc['portal'] == in_row['portal']) & (kc['eventname'] == in_row['eventname'])].all(1).any():
		return "Known Correct"
	elif kc.loc[(kc['proot'] == in_row['proot']) & (kc['eventname'] == in_row['eventname'])].all(1).any():
		return "Known Incorrect" # at this point, we know the portals do not match, so if the roots match then it's wrong
	else:
		return "Unknown"


def getKnownCorrectPairs( data):
	threshold = 1
	return data[data['freq'] > threshold]

# sample usecase 
def main():
	# first, read in the results we're going to base correctness on 
	dat = processFile('test.csv')
	dat['freq'] = dat.groupby(['portal','eventname'])['proot'].transform('count') # add the frequency with which each row appears
	dat = dat.drop_duplicates()

	correct_vals = getKnownCorrectPairs(dat)


	# now, read in a new file to check over
	# add a column specifying the correctness of each row
	test_input = processFile('in_test.csv')
	test_input = test_input.drop_duplicates()
	test_input['Correctness'] = test_input.apply(lambda row: rowCorrectness(row, correct_vals), axis=1)

	print(test_input)

main()







# old bad code, list comprehension style



# portals = dat.loc[:, 'portal']
# eventnames = dat.loc[:, 'eventname']
# eventnames.unique()

# roots = portals.map( getPortalRoot)
# dat['proot'] = roots # add a root column



# # for each root, get a list of portals
# # can be accessed per index 
# [(i, dat.loc[dat['proot'] == i].loc[:, 'portal'].unique()) for i in roots.unique()]

# # for each root, get a list of eventnames
# [(i, dat.loc[dat['proot'] == i].loc[:, 'eventname'].unique()) for i in roots.unique()]

# # for each portal, get a list of eventnames
# # this is SUPER useless
# [(i, dat.loc[dat['portal'] == i].loc[:, 'eventname'].unique()) for i in portals.unique()]



# # for each (root, eventname) pair, count the number of different 
# # portals it appears in
# list(filter( lambda z: z[2] > 0, [(i, j, len(dat.loc[dat['proot'] == i].loc[dat['eventname'] == j].loc[:, 'portal'].unique())) for i in roots.unique() for j in eventnames.unique()]))

# # foreach (portal, eventname) pair, count the number of each (none > 2 right now)
# # this is SUPER slow, would need to be faster to actually be used
# list(filter( lambda z: z[2] > 1, [(i, j, len(dat.loc[dat['portal'] == i].loc[dat['eventname'] == j].loc[:, 'proot'].unique())) for i in portals.unique() for j in eventnames.unique()]))


# [(i, j, len(dat.loc[dat['portal'] == i].loc[dat['eventname'] == j].loc[:, 'proot'].unique())) for i in portals.unique() for j in df_root_ename.loc[df_root_ename['a'] == getPortalRoot(i)]['b'].tolist()[0]]

# # better way of doing the original run
# # i realize now that the reason nothing is showing up as appearing multiple times is that i filtered the list to be unique before pasting it into the file 
# list(filter( lambda z: z[2] > 1, [(i, j, len(dat.loc[dat['portal'] == i].loc[dat['eventname'] == j].loc[:, 'proot'].unique())) for i in portals.unique() for j in df_root_ename.loc[df_root_ename['a'] == getPortalRoot(i)]['b'].tolist()[0]]))




# ardat = [[i, dat.loc[dat['proot'] == i].loc[:, 'eventname'].unique()] for i in roots.unique()]
# from pandas import DataFrame
# df_root_ename = DataFrame.from_records(ardat)


# threshold = 0 # number of appearaces above which we "know" the (portal, eventname) is correct 
# correctVals = DataFrame.from_records(list(filter( lambda z: z[2] > threshold, [(i, j, len(dat.loc[dat['portal'] == i].loc[dat['eventname'] == j].loc[:, 'proot'].unique())) for i in portals.unique() for j in df_root_ename.loc[df_root_ename['a'] == getPortalRoot(i)]['b'].tolist()[0]])))
# correctVals.columns = ['portal', 'ename', 'freq']
# correct_portal_enames = correctVals.drop('freq', axis=1)


# at this point, let's read in another list and check for existence
# checking for correctness is easy
# for incorrectness, let's say does not exist, but does exist in (root, ename) dataframe (df_root_ename)
