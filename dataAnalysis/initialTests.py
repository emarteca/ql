import pandas as pd 
import numpy as np
import matplotlib.pyplot as plt

# given the name of a portal, split the string up to find the name of the root
def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

# given a csv of (portal, eventname) pairs, process it into a dataframe of the correct shape
# named columns, and including the portal root as a column
def processFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['proot', 'portal', 'eventname']
	# result['proot'] = result.apply(lambda row: getPortalRoot(row['portal']), axis=1)
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

def getKnownIncorrectForPortal( portal_name, cvs):
	# the incorrect list for a portal is
	# total list for the same root - list of correct vals for the portal
	return np.setdiff1d(cvs.loc[cvs['proot'] == getPortalRoot(portal_name)].loc[:,'eventname'], cvs.loc[cvs['portal'] == portal_name].loc[:,'eventname'].values)

def getKnownCorrectForPortal( portal_name, cvs):
	return cvs.loc[cvs['portal'] == portal_name].loc[:,'eventname'].values

def plotHistProotEname( proot, eventname, df, topToPlot = -1, logscale = False):
	plotme = df.loc[(df['proot'] == proot) & (df['eventname'] == eventname)][['portal','freq']].sort_values(['freq'])
	if topToPlot > -1:
		plotme = plotme.tail(topToPlot)
	graph = plotme.plot(kind='bar',x='portal',y='freq')
	plt.xlabel('Portal')
	plt.ylabel('Frequency')
	if logscale:
		plt.yscale('log')
	plt.title('Frequency of listeners to "' + eventname + '" on root ' + proot, fontsize=10)
	plt.gca().axes.xaxis.set_ticklabels(list(range(len(plotme))))
	plt.legend().remove()
	# make a custom "legend" (i.e. textbox) of the portals actually on this graph
	portals = list( plotme['portal'].values)
	plt.text(0, plt.ylim()[1]*3./4, getLegendList(portals), fontsize=6)
	plt.show()

def getLegendList( pList):
	ret = ""
	for i in range(len(pList)):
		ret += str(i) + ": " + pList[i] + "\n"
	return ret

def printDFToFile( df, filename):
	f = open(filename, 'w');
	f.write(df.to_csv(index = False))
	f.close()

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
	test_input['Known Incorrect'] = test_input.apply(lambda row: getKnownIncorrectForPortal(row['portal'], correct_vals), axis=1)
	test_input['Known Correct'] = test_input.apply(lambda row: getKnownCorrectForPortal(row['portal'], correct_vals), axis=1)

	print(test_input)

	plotHistProotEname( 'fs', 'data', dat, 10)

main()

