import pandas as pd 

def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

dat = pd.read_csv('test.csv', sep = ',', header=None)
dat.columns = ['portal', 'eventname']

portals = dat.loc[:, 'portal']
eventnames = dat.loc[:, 'eventname']
eventnames.unique()

roots = portals.map( getPortalRoot)
dat['proot'] = roots # add a root column


# for each root, get a list of portals
# can be accessed per index 
[(i, dat.loc[dat['proot'] == i].loc[:, 'portal'].unique()) for i in roots.unique()]

# for each root, get a list of eventnames
[(i, dat.loc[dat['proot'] == i].loc[:, 'eventname'].unique()) for i in roots.unique()]

# for each portal, get a list of eventnames
# this is SUPER useless
[(i, dat.loc[dat['portal'] == i].loc[:, 'eventname'].unique()) for i in portals.unique()]



# for each (root, eventname) pair, count the number of different 
# portals it appears in
list(filter( lambda z: z[2] > 0, [(i, j, len(dat.loc[dat['proot'] == i].loc[dat['eventname'] == j].loc[:, 'portal'].unique())) for i in roots.unique() for j in eventnames.unique()]))

# foreach (portal, eventname) pair, count the number of each (none > 2 right now)
# this is SUPER slow, would need to be faster to actually be used
list(filter( lambda z: z[2] > 1, [(i, j, len(dat.loc[dat['portal'] == i].loc[dat['eventname'] == j].loc[:, 'proot'].unique())) for i in portals.unique() for j in eventnames.unique()]))
