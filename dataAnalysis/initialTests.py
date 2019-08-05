import pandas as pd 
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import binom
import re
from collections import namedtuple
from collections import Counter
import csv

pd.options.mode.chained_assignment = None # remove chained assignment warnings (they dont fit my use case)


# ----------------------------------------------------------------------------------------------------------------------- processing functions
# given the name of a portal, split the string up to find the name of the root
def getPortalRoot( portal):
	return portal[ portal.index('root') + len('root ') : portal.index(')')]

# given a csv of (root, portal, eventname, projcount) pairs, process it into a dataframe of the correct shape
# named columns, and including the portal root as a column
# we also add the processed columns we want (frequency, etc)
def processFile( fileName):
	result = pd.read_csv(fileName, sep = ',', header=None)
	result.columns = ['proot', 'portal', 'eventname', 'projcount']
	result.replace(np.nan, 'NaN', regex=True, inplace=True)
	result['freq'] = result.groupby(['portal','eventname', 'proot'])['projcount'].transform('sum') # add the frequency with which each row appears
	result.drop(['projcount'], inplace=True, axis=1) # this information only makes sense to keep when we also have the project saved, i.e. in the "with files" version
	result.drop_duplicates(inplace=True)
	result['freq_e'] = result.groupby(['proot','eventname'])['freq'].transform('sum') # find frequency with which each event appears for the root
	result['freq_p'] = result.groupby(['proot','portal'])['freq'].transform('sum')	  # same for the portals
	return result

# when we have a dataframe which includes the path to the origin project for each 
# (portal, eventname) pair, this function returns the path for a particular pair
def getPathForPortalEname( df_with_path, portal, ename):
	return df_with_path[(df_with_path['portal'] == portal) & (df_with_path['eventname'] == ename)]['path'] 

# print dataframe df to file specified
def printDFToFile( df, filename):
	f = open(filename, 'w');
	f.write(df.to_csv(index = False))
	f.close()

# print the results in the "category" column labelled as the category specified 
# out to a file (either appending or replacing the entire contents of the file, as specified by the optional "append" argument)
# we're printing in the format to match the output of the corresponding QL query, so
# as a list of (portal, eventname) pairs, pre/suffixed with "", and without printing the headers
def printCatResultsToFile(df, filename, category, append=True):
	write_mode = 'a' if append else 'w'
	f = open(filename, write_mode)
	toprint = df[df['category'] == category][['portal', 'eventname']]
	f.write(toprint.to_csv(index=False, header=False, quoting=csv.QUOTE_ALL))
	f.close()

# ------------------------------------------------------------------------------------------------------------------------------------- graphing

# plot a histogram of all the portals with listeners for a specified eventname, on a specified root
# additional, optional arguments are:
# topToPlot: if a specified positive integer, we plot the "topToPlot" most frequent portals 
# logscale: do we logscale the y axis?
# showTickLabels: the xticklabels are the portal names so they are very unweidly (theyre also shown as a legend and not on the xaxis)
#				  it only makes sense to have them when there are not many portals, or it quickly becomes unreadable 
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

# plot a histogram of the events for which listeners are registered for a specified portal
# note that this is root-specific even though not explicitly encoded, since the portals are root-specific
def plotHistPortalEnames( portal, df):
	plotme = df.loc[df['portal'] == portal][['eventname', 'freq']].sort_values(['freq'])
	graph = plotme.plot(kind='bar',x='eventname',y='freq')
	plt.xlabel('Event name')
	plt.ylabel('Frequency')
	plt.title('Frequency of each listener on portal ' + portal, fontsize=10)
	plt.legend().remove()
	plt.show()

# helper function for getting the legend for the portal histogram (legend is the list of portals)
def getLegendList( pList):
	ret = ""
	for i in range(len(pList)):
		ret += str(i) + ": " + pList[i] + "\n"
	return ret

# ---------------------------------------------------------------------------------------------------------------------------------- computing broken/correct

# --------------------------------------------------------------------------------------------------------------- the core processing functions

# sum up the tail of the frequency histograms for both portals and eventnames respectively
# this is just a cumulative sum (where the duplicate frequencies are included in the count for this frequency)
# so, for example, if there are 3 events with frequency 1 and 1 with frequency 2, the LTEFreq for those with frequency 1
# would all be 3, and the LTEFreq for the one with frequency 2 would be 5 (2 + 3*1)
def addLTEFreqsToFrame( prdat): 
	prdat.sort_values(['freq'], inplace=True)
	addCumFreqsToFrame(prdat, 'eventname', 'ltefreq_p')
	addCumFreqsToFrame(prdat, 'portal', 'ltefreq_e')

# compute the cumulative frequencies described above
def addCumFreqsToFrame( prdat, col_name, out_col_name):
	reldup = (~prdat[[col_name, 'freq']].duplicated()).astype(int) # compute the rows which are duplicate frequencies
	# now, compute the sum of all the duplicate frequencies (for each event)
	# the multiplication by reldup is a hack so that the cumulative frequency includes duplicate frequencies but only once
	# the result is that the first of a duplicate row (i.e. duplicate frequency for an event) has the total sum of all its duplicates
	# and the rest of the duplicate rows have intermsum = 0. then, when we compute the cumulative sum they all have the same value
	# also note that this only works because we sort the frame by frequency before calling this function (as in addLTEFreqsToFrame)
	prdat['intermsum'] = prdat.groupby([col_name, 'freq'])['freq'].transform('sum')*reldup 
	prdat[out_col_name] = prdat.groupby([col_name])['intermsum'].transform('cumsum')

# function to determine if a particular (portal, eventname) pair is broken
# this is part of a row which includes the relevant frequencies, so basically this 
# is just a wrapper for the binomial CDF computations and relevant comparisons
# returns a string specifying the category (broken/correct/unknown)
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

# adds the category to each row of the dataframe
def addCatToFrame( prdat, prare_e, prare_p, pconf):
	prdat['category'] = prdat.apply(categorizePortalEnamePair, args=(prare_e, prare_p, pconf), axis=1)

# --------------------------------------------------------------------------------------------------------------------done core processing functions

# function to avoid having to type "prdat[prdat["category"] == category]"
# just returns the slice of the dataframe with the specified category
def getCategoryFromCategorizedFrame( prdat, category):
	return prdat[prdat['category'] == category]

# return a dataframe which is the root-specific results (for the root passed in), 
# with the correct/broken results included
def getRootSpecificDFWithBroken( df, proot, prare_e, prare_p, pconf):
	prdat = df[df['proot'] == proot][['portal', 'eventname', 'freq', 'freq_e', 'freq_p']]
	addLTEFreqsToFrame(prdat)
	addCatToFrame(prdat, prare_e, prare_p, pconf)
	return prdat

# takes in a dataframe, which we have to get the list of proots from
# count these up (i.e. list in order of most to less frequent), and then access
# the relevant indices and return an array of these positions
def getRootsAtFreqIndices( df, inds):
	proots = Counter(df['proot'].values).most_common(max(inds) + 1) # get the list of roots, sorted by appearance frequency
	return [proots[i][0] for i in inds] # get the corresponding list of roots (the [0] is since in Counter it's a 
										# tuple with the freq, but we only want the names)

# returns a dictionary of dataframes (where the key is the root name) 
# for the roots specified by the list of indices
def getDFsFromRootIndices( df, inds):
	return getDFsFromRootNames( df, getRootsAtFreqIndices(df, inds))

# create a dictionary where the root names are keys and the values are 
# the dataframe for that root
def getDFsFromRootNames( df, rootNames):
	return {name: df[df['proot'] == name] for name in rootNames} 

# run addLTEsToFrame over every element in the dictionary of dataframes
def addLTEsToFramesInDict( dcf):
	return {name: addLTEFreqsToFrame( df) for name, df in dcf.items()}

# ------------------------------------------------------------------------------------------------------------------------- experiment
# code for running the experiments
# runner wrapper and main() that's a sample usecase

Ps = namedtuple("Ps", "prare_e prare_p pconf")

# start with just a list of packages, but would be trivial to change this to be a list of 
# indices, or make it just run over all the packages
# sample use: runTests(dat, [Ps(0.05, 0.05, 0.05)], ['fs', 'http', 'net'])
def runTests( df, param_configs, pkgs_to_test):
	# now we need to actually run the experiment
	# run it over all the configs provided, for each package listed
	for ps in param_configs:
		filename = "pe" + str(ps.prare_e) + "_pp" + str(ps.prare_p) + "_pc" + str(ps.pconf) + "_.csv"
		append = False
		for pkg in pkgs_to_test:
			cur_frame = df[df['proot'] == pkg]
			addLTEFreqsToFrame(cur_frame)
			print("Done adding LTE\n")
			addCatToFrame( cur_frame, ps.prare_e, ps.prare_p, ps.pconf)
			# printDFToFile( cur_frame, filename)
			printCatResultsToFile(cur_frame, "correct_" + filename, "Correct", append)
			printCatResultsToFile(cur_frame, "broken_" + filename, "Broken", append)
			printCatResultsToFile(cur_frame, "unknown_" + filename, "Unknown", append)
			append = True
			print("Done running: " + filename + "\n") 



# sample usecase 
def main():
	# first, read in the results we're going to base correctness on 
	dat = processFile('merged_data.out')

	print("Done reading in the data\n\n")
	
	# then, set up an experiment and run it
	param_configs = [Ps(0.05, 0.05, 0.05)]
	pkgs_to_test = ['fs', 'http', 'net']
	runTests(dat, param_configs, pkgs_to_test)

	print("Done the tests!")

main()