import pandas as pd 
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import binom
import re

pd.options.mode.chained_assignment = None # remove chained assignment warnings (they dont fit my use case)

# given the name of a portal, split the string up to find the name of the root
def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

def getPortalDepthRoot( portal, depth):
    try:
        return portal[ [ m.start() for m in re.finditer('\(', portal)][-depth]: portal.find(')')]
    except IndexError:
        return portal

# given a csv of (portal, eventname) pairs, process it into a dataframe of the correct shape
# named columns, and including the portal root as a column
def processFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['proot', 'portal', 'eventname', 'projcount']
	result['proot_d2'] = result.apply(lambda row: getPortalDepthRoot(row['portal'], 2), axis=1)
	return result.replace(np.nan, 'NaN', regex=True)

def getPathForPortalEname( df_with_path, portal, ename):
	return df_with_path[(df_with_path['portal'] == portal) & (df_with_path['eventname'] == ename)]['path'] 

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

def getRootSpecificDFWithBroken( df, proot, prare_e, prare_p, pconf):
	prdat = df[df['proot'] == proot][['portal', 'eventname', 'freq', 'freq_e', 'freq_p']]
	prdat['broken'] = prdat.apply(lambda row: isAPortalEnamePairBroken(prdat[(prdat['portal'] == row['portal']) & (prdat['eventname'] == row['eventname'])], prare_e, prare_p, pconf, row['eventname'], row['portal']), axis=1)
	return prdat

# this is a temp function, should just be here for working on the terminal
# don't use it in the above function getProbBuggyPortalEnamePairs as it would 
# cause unnecessary temp variables of the whole dataframe 
def addBrokenToFrame( prdat, prare_e, prare_p, pconf):
	prdat['broken'] = prdat.apply(isAPortalEnamePairBroken, args=(prare_e, prare_p, pconf), axis=1)

def addCorrectToFrame( prdat, prare_e, prare_p, pconf):
	prdat['correct'] = prdat.apply(isAPortalEnamePairCorrect, args=(prare_e, prare_p, pconf), axis=1)

def isAPortalEnamePairBroken( row, prare_e, prare_p, pconf):
	# temp = df[(df['portal'] == portal) & (df['eventname'] == ename)]
	freq_eandp = row['freq']
	freq_sumeandp = row['ltefreq_p']
	freq_eandsump = row['ltefreq_e']
	freq_e = row['freq_e']
	freq_p = row['freq_p']
	# compute the binomial cdfs with the relevant parameters
	return ((binom.cdf( freq_sumeandp, freq_p, prare_p) < pconf) and (binom.cdf( freq_eandsump, freq_e, prare_e) < pconf))
	# return [binom.cdf( freq_eandp, freq_p, prare), binom.cdf( freq_eandp, freq_e, prare)]

def isAPortalEnamePairCorrect( row, prare_e, prare_p, pconf):
	# temp = df[(df['portal'] == portal) & (df['eventname'] == ename)]
	freq_eandp = row['freq']
	freq_e = row['freq_e']
	freq_p = row['freq_p']
	# compute the binomial cdfs with the relevant parameters
	return ((binom.cdf( (freq_p - freq_eandp), freq_p, 1 - prare_p) < pconf) and (binom.cdf( (freq_e - freq_eandp), freq_e, 1 - prare_e) < pconf)
		and freq_eandp > 10)

def categorizePortalEnamePair( row, prare_e, prare_p, pconf):
	freq_eandp = row['freq']
	freq_sumeandp = row['ltefreq_p']
	freq_eandsump = row['ltefreq_e']
	freq_e = row['freq_e']
	freq_p = row['freq_p']
	if ((binom.cdf( freq_sumeandp, freq_p, prare_p) < pconf) and (binom.cdf( freq_eandsump, freq_e, prare_e) < pconf)):
		return 'Broken'
	elif ((binom.cdf( (freq_p - freq_eandp), freq_p, 1 - prare_p) < pconf) and (binom.cdf( (freq_e - freq_eandp), freq_e, 1 - prare_e) < pconf) and freq_eandp > 10):
		return 'Correct'
	else:
		return 'Unknown'

def addCatToFrame( prdat, prare_e, prare_p, pconf):
	prdat['category'] = prdat.apply(categorizePortalEnamePair, args=(prare_e, prare_p, pconf), axis=1)

def getCategoryFromCategorizedFrame( prdat, category):
	return prdat[prdat['category'] == category]

def addColumnForMatchingPortalEnames( df, df_to_comp, new_col_name):
	# assume the df_to_comp has columns for 'portal' and 'eventname'
	# and that these are the only columns we have to compare with
	df[new_col_name] = df[['portal','eventname']].apply(tuple, 1).isin(df_to_comp.apply(tuple, 1))


def processKnownPortalEnameFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['portal', 'eventname']
	return result

# takes in a dataframe, which we have to get the list of proots from
# count these up (i.e. list in order of most to less frequent), and then access
# the relevant indices and return an array of these positions
def getRootsAtFreqIndices( df, inds):
	proots = Counter(df['proot'].values).most_common(max(inds) + 1) # get the list of roots, sorted by appearance frequency
	return [proots[i][0] for i in inds] # get the corresponding list of roots (the [0] is since in Counter it's a tuple with the freq, but we only want the names)

def getDFsFromRootIndices( df, inds):
	return getDFsFromRootNames( df, getRootsAtFreqIndices(df, inds))

# create a dictionary where the root names are keys and the values are 
# the dataframe for that root
def getDFsFromRootNames( df, rootNames):
	return {name: df[df['proot'] == name] for name in rootNames} 

def addLTEsToFramesInDict( dcf):
	return {name: addLTEFreqsToFrame( df) for name, df in dcf.items()}

# return the sum of frequencies of all rows where the value of 
# a particular column is <= a specified value
# will be used applied to each row in a dataframe to get the cumulative sum
# for all portals and events 
def conditionalFreqSumForLTEcol( df, val_to_comp):
	return df[df['freq'] <= val_to_comp]['freq'].sum()

def addLTEFreqsToFrame( prdat): 
	prdat = prdat.sort_values(['freq'])
	addCumFreqsToFrame(prdat, 'eventname', 'ltefreq_p')
	addCumFreqsToFrame(prdat, 'portal', 'ltefreq_e')

def addCumFreqsToFrame( prdat, col_name, out_col_name):
	reldup = (~prdat[[col_name, 'freq']].duplicated()).astype(int)
	prdat['intermsum'] = prdat.groupby([col_name, 'freq'])['freq'].transform('sum')*reldup
	prdat[out_col_name] = prdat.groupby([col_name])['intermsum'].transform('cumsum')




from collections import namedtuple

Ps = namedtuple("Ps", "prare_e prare_p pconf")

# start with just a list of packages, but would be trivial to change this to be a list of 
# indices, or make it just run over all the packages
# sample use: runTests(dat, [Ps(0.05, 0.05, 0.05)], ['fs', 'http'])
def runTests( df, param_configs, pkgs_to_test):
	pkg_frames = getDFsFromRootNames( df, pkgs_to_test)
	addLTEsToFramesInDict( pkg_frames)
	# now we need to actually run the experiment
	# run it over all the configs provided
	for ps in param_configs:
		for name, pdf in pkg_frames.items():
			addCatToFrame( pdf, ps.prare_e, ps.prare_p, ps.pconf)
			filename = name + "_pe" + str(ps.prare_e) + "_pp" + str(ps.prare_p) + "_pc" + str(ps.pconf) + "_.csv"
			printDFToFile( pdf, filename)
			print("\nDone running: " + filename) 



# sample usecase 
def main():
	# first, read in the results we're going to base correctness on 
	dat = processFile('test.csv')
	dat['freq'] = dat.groupby(['portal','eventname', 'proot'])['projcount'].transform('sum') # add the frequency with which each row appears
	dat = dat.drop(['projcount'], axis=1) # this information only makes sense to keep when we also have the project saved, i.e. in the "with files" version
	dat = dat.drop_duplicates()
	dat['freq_e'] = dat.groupby(['proot','eventname'])['freq'].transform('sum') # find frequency with which each event appears for the root
	dat['freq_p'] = dat.groupby(['proot','portal'])['freq'].transform('sum') # find frequency with which each portal appears for the root

	correct_vals = getKnownCorrectPairs(dat)


	# now, read in a new file to check over
	# add a column specifying the correctness of each row
	test_input = processFile('in_test.csv')
	test_input = test_input.drop_duplicates()
	test_input['Correctness'] = test_input.apply(lambda row: rowCorrectness(row, correct_vals), axis=1) # don't do it this way, for efficiency (but this is old code)
	test_input['Known Incorrect'] = test_input.apply(lambda row: getKnownIncorrectForPortal(row['portal'], correct_vals), axis=1)
	test_input['Known Correct'] = test_input.apply(lambda row: getKnownCorrectForPortal(row['portal'], correct_vals), axis=1)

	print(test_input)

	plotHistProotEname( 'fs', 'data', dat, 10)


main()


addLTEFreqsToFrame(fsdat)
addLTEFreqsToFrame(netdat)
addLTEFreqsToFrame(siodat)
addLTEFreqsToFrame(siocdat)
addLTEFreqsToFrame(httpdat)

addBrokenToFrame(fsdat, prare_e, prare_p, pconf)
addBrokenToFrame(netdat, prare_e, prare_p, pconf)
addBrokenToFrame(siodat, prare_e, prare_p, pconf)
addBrokenToFrame(siocdat, prare_e, prare_p, pconf)
addBrokenToFrame(httpdat, prare_e, prare_p, pconf)

printDFToFile(fsdat[fsdat['broken']].append(netdat[netdat['broken']]).append(siodat[siodat['broken']]).append(siocdat[siocdat['broken']]).append(httpdat[httpdat['broken']]
	.append(cprocdat[cprocdat['broken']]).append(zlibdat[zlibdat['broken']]).append(httpsdat[httpsdat['broken']])), 
	'fs_net_sio_sioc_http_childproc_zlib_https_pe0.06_pp0.04_pc_0.04_diagnosis.csv')

printDFToFile(fsdat[fsdat['broken'] == False].append(netdat[netdat['broken'] == False]).append(siodat[siodat['broken'] == False]).append(siocdat[siocdat['broken'] == False]).append(httpdat[httpdat['broken'] == False]), 
	'fs_net_sio_sioc_http_pe0.06_pp0.05_pc_0.04_notflagged.csv')

printDFToFile(fsdat[fsdat['broken'] == False], 'fs_pe0.06_pp0.05_pc_0.04_notflagged.csv')
printDFToFile(netdat[netdat['broken'] == False], 'net_pe0.06_pp0.05_pc_0.04_notflagged.csv')
printDFToFile(siodat[siodat['broken'] == False], 'sio_pe0.06_pp0.05_pc_0.04_notflagged.csv')
printDFToFile(siocdat[siocdat['broken'] == False], 'sioc_pe0.06_pp0.05_pc_0.04_notflagged.csv')
printDFToFile(httpdat[httpdat['broken'] == False], 'http_pe0.06_pp0.05_pc_0.04_notflagged.csv')




from collections import Counter

proots = dat['proot'].values
pcount = Counter(proots)
pcount.most_common(75)






vorpaldat = dat[dat['proot'] == 'vorpal']
nvd3dat = dat[dat['proot'] == 'nvd3']
superagentproxydat = dat[dat['proot'] == 'superagent-proxy']
busiodat = dat[dat['proot'] == 'bus.io']
jsextenddat = dat[dat['proot'] == 'js-extend']
etchdat = dat[dat['proot'] == 'etch']
mongodbdat = dat[dat['proot'] == 'mongodb']
protractordat = dat[dat['proot'] == 'protractor']
hammerjsdat = dat[dat['proot'] == 'hammerjs']
appendtreedat = dat[dat['proot'] == 'append-tree']
sysdat = dat[dat['proot'] == 'sys']
liedat = dat[dat['proot'] == 'lie']
bluebirdat = dat[dat['proot'] == 'bluebird']
sinondat = dat[dat['proot'] == 'sinon']
webkitgtkdat = dat[dat['proot'] == 'webkitgtk']
leapjsdat = dat[dat['proot'] == 'leapjs']
treportdat = dat[dat['proot'] == 'treport']
telnetdat = dat[dat['proot'] == 'telnet']
throughdat = dat[dat['proot'] == 'through']
fstreamdat = dat[dat['proot'] == 'fstream']
through2dat = dat[dat['proot'] == 'through2']
browserifydat = dat[dat['proot'] == 'browserify']

jquerydat = dat[dat['proot'] == 'jquery']
addLTEFreqsToFrame(jquerydat)
addBrokenToFrame(jquerydat, prare_e, prare_p, pconf)

addLTEFreqsToFrame(vorpaldat)
addLTEFreqsToFrame(nvd3dat)
addLTEFreqsToFrame(superagentproxydat)
addLTEFreqsToFrame(busiodat)
addLTEFreqsToFrame(jsextenddat)
addLTEFreqsToFrame(etchdat)
addLTEFreqsToFrame(mongodbdat)
addLTEFreqsToFrame(protractordat)
addLTEFreqsToFrame(hammerjsdat)
addLTEFreqsToFrame(appendtreedat)
addLTEFreqsToFrame(sysdat)
addLTEFreqsToFrame(liedat)
addLTEFreqsToFrame(bluebirdat)
addLTEFreqsToFrame(sinondat)
addLTEFreqsToFrame(webkitgtkdat)
addLTEFreqsToFrame(leapjsdat)
addLTEFreqsToFrame(treportdat)
addLTEFreqsToFrame(telnetdat)
addLTEFreqsToFrame(throughdat)
addLTEFreqsToFrame(fstreamdat)
addLTEFreqsToFrame(through2dat)
addLTEFreqsToFrame(browserifydat)

addBrokenToFrame(vorpaldat, prare_e, prare_p, pconf)
addBrokenToFrame(nvd3dat, prare_e, prare_p, pconf)
addBrokenToFrame(superagentproxydat, prare_e, prare_p, pconf)
addBrokenToFrame(busiodat, prare_e, prare_p, pconf)
addBrokenToFrame(jsextenddat, prare_e, prare_p, pconf)
addBrokenToFrame(etchdat, prare_e, prare_p, pconf)
addBrokenToFrame(mongodbdat, prare_e, prare_p, pconf)
addBrokenToFrame(protractordat, prare_e, prare_p, pconf)
addBrokenToFrame(hammerjsdat, prare_e, prare_p, pconf)
addBrokenToFrame(appendtreedat, prare_e, prare_p, pconf)
addBrokenToFrame(sysdat, prare_e, prare_p, pconf)
addBrokenToFrame(liedat, prare_e, prare_p, pconf)
addBrokenToFrame(bluebirdat, prare_e, prare_p, pconf)
addBrokenToFrame(sinondat, prare_e, prare_p, pconf)
addBrokenToFrame(webkitgtkdat, prare_e, prare_p, pconf)
addBrokenToFrame(leapjsdat, prare_e, prare_p, pconf)
addBrokenToFrame(treportdat, prare_e, prare_p, pconf)
addBrokenToFrame(telnetdat, prare_e, prare_p, pconf)
addBrokenToFrame(throughdat, prare_e, prare_p, pconf)
addBrokenToFrame(fstreamdat, prare_e, prare_p, pconf)
addBrokenToFrame(through2dat, prare_e, prare_p, pconf)
addBrokenToFrame(browserifydat, prare_e, prare_p, pconf)




