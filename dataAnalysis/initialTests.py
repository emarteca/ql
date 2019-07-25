import pandas as pd 
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import binom

# given the name of a portal, split the string up to find the name of the root
def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

# given a csv of (portal, eventname) pairs, process it into a dataframe of the correct shape
# named columns, and including the portal root as a column
def processFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['proot', 'portal', 'eventname']
	# result['proot'] = result.apply(lambda row: getPortalRoot(row['portal']), axis=1)
	return result.replace(np.nan, 'NaN', regex=True)

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

def plotHistProotEname( proot, eventname, df, topToPlot = -1, logscale = False, showTickLabels = True):
	plotme = df.loc[(df['proot'] == proot) & (df['eventname'] == eventname)][['portal','freq']].sort_values(['freq'])
	if topToPlot > -1:
		plotme = plotme.tail(topToPlot)
	graph = plotme.plot(kind='bar',x='portal',y='freq')
	plt.xlabel('Portal')
	plt.ylabel('Frequency')
	if logscale:
		plt.yscale('log')
	plt.title('Frequency of listeners to "' + eventname + '" on root ' + proot, fontsize=10)
	plt.legend().remove()
	# 
	if showTickLabels:
		plt.gca().axes.xaxis.set_ticklabels(list(range(len(plotme))))
		# make a custom "legend" (i.e. textbox) of the portals actually on this graph
		portals = list( plotme['portal'].values)
		plt.text(0, plt.ylim()[1]*1./4, getLegendList(portals), fontsize=6)
	else:
		plt.gca().axes.xaxis.set_ticklabels([])
	plt.show()

def plotHistPortalEnames( portal, df):
	plotme = df.loc[df['portal'] == portal][['eventname', 'freq']].sort_values(['freq'])
	graph = plotme.plot(kind='bar',x='eventname',y='freq')
	plt.xlabel('Event name')
	plt.ylabel('Frequency')
	plt.title('Frequency of each listener on portal ' + portal, fontsize=10)
	plt.legend().remove()
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


# for a given root, find the potentially broken (portal, ename) pairs
# given some specified thresholds for identifying these
# right now these are placeholder thresholds, but hopefully most of this framework
# is reusable when we figure out more accurate thresholds
# for now keep prare for enames and portals the same, and pconf for enames and portals the same
# but note that this may be subject to change
def getProbBuggyPortalEnamePairs( df, proot, prare_e, prare_p, pconf):
	# from albert: 
	# take prare = 5% (for example)
	# B(number of ename AND portal, number of portal, prare) < pconfidence (could also be 5%)
	# and
	# B(number of ename AND portal, number of events, prare) < pconfidence (commonly used as 5%)
	# where B is the cumulative binomial distribution fct
	prdat = df[df['proot'] == proot][['portal', 'eventname', 'freq', 'freq_e', 'freq_p']]
	prdat['broken'] = prdat.apply(lambda row: isAPortalEnamePairBroken(prdat[(prdat['portal'] == row['portal']) & (prdat['eventname'] == row['eventname'])], prare_e, prare_p, pconf, row['eventname'], row['portal']), axis=1)
	return prdat[prdat['broken']]

# this is a temp function, should just be here for working on the terminal
# don't use it in the above function getProbBuggyPortalEnamePairs as it would 
# cause unnecessary temp variables of the whole dataframe 
def addBrokenToFrame( prdat, prare_e, prare_p, pconf):
	prdat['broken'] = prdat.apply(lambda row: isAPortalEnamePairBroken(prdat[(prdat['portal'] == row['portal']) & (prdat['eventname'] == row['eventname'])], prare_e, prare_p, pconf, row['eventname'], row['portal']), axis=1)
	return prdat

def isAPortalEnamePairBroken( temp, prare_e, prare_p, pconf, ename, portal):
	# temp = df[(df['portal'] == portal) & (df['eventname'] == ename)]
	freq_eandp = temp[['freq']].values[0][0]
	freq_e = temp[['freq_e']].values[0][0]
	freq_p = temp[['freq_p']].values[0][0]
	# compute the binomial cdfs with the relevant parameters
	return ((binom.cdf( freq_eandp, freq_p, prare_p) < pconf) and (binom.cdf( freq_eandp, freq_e, prare_e) < pconf))
	# return [binom.cdf( freq_eandp, freq_p, prare), binom.cdf( freq_eandp, freq_e, prare)]

# sample usecase 
def main():
	# first, read in the results we're going to base correctness on 
	dat = processFile('test.csv')
	dat['freq'] = dat.groupby(['portal','eventname'])['proot'].transform('count') # add the frequency with which each row appears
	dat = dat.drop_duplicates()
	dat['freq_e'] = dat.groupby(['proot','eventname'])['freq'].transform('sum') # find frequency with which each event appears for the root
	dat['freq_p'] = dat.groupby(['proot','portal'])['freq'].transform('sum') # find frequency with which each portal appears for the root

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




