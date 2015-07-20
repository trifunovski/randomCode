from __future__ import division
import numpy as np
from scipy.stats import cumfreq
import pylab as plt


bandupNew = []
banddownNew = []
f = open('shadow.config.xml', 'r')
for line in f:
    if("relayexit" in line):
        ind1 = line.find("bandwidthdown")+15
        ind2 = line.find('"',ind1)
        if ind1>14:
            num = int(line[ind1:ind2])
            banddownNew.append(num)
        ind1 = line.find("bandwidthup")+13
        ind2 = line.find('"',ind1)
        if ind1>14:
            num = int(line[ind1:ind2])
            bandupNew.append(num)

print banddownNew
print bandupNew

bandupOld = []
banddownOld = []

k = open('hosts.xml', 'r')
for line in k:
    if("exit" in line and "nonexit" not in line):
        ind1 = line.find("bandwidthdown")+15
        ind2 = line.find('"',ind1)
        if ind1>14:
            num = int(line[ind1:ind2])
            banddownOld.append(num)
        ind1 = line.find("bandwidthup")+13
        ind2 = line.find('"',ind1)
        if ind1>14:
            num = int(line[ind1:ind2])
            bandupOld.append(num)

print banddownOld
print bandupOld


def cf(d): return plt.arange(1.0,float(len(d))+1.0)/float(len(d))

def getcdf(data, shownpercentile=0.99, maxpoints=100000.0):
    data.sort()
    frac = cf(data)
    k = len(data)/maxpoints
    x, y, lasty = [], [], 0.0
    for i in xrange(int(round(len(data)*shownpercentile))):
        if i % k > 1.0: continue
        assert not np.isnan(data[i])
        x.append(data[i])
        y.append(lasty)
        x.append(data[i])
        y.append(frac[i])
        lasty = frac[i]
    return x, y


x, y = getcdf(banddownOld)
plt.plot(x,y,label="banddownOld")
x, y = getcdf(banddownNew)
plt.plot(x,y,label="banddownNew")
x, y = getcdf(bandupOld)
plt.plot(x,y,label="bandupOld")
x, y = getcdf(bandupNew)
plt.plot(x,y,label="bandupNew")
plt.legend(loc="lower right")
plt.show()
