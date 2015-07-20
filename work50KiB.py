import matplotlib, pylab
import numpy

f = open('50KiB.tpf', 'r')
full = []
firstByte = []

for line in f:
    ind1 = line.find("CONNECT=")+8
    ind2 = line.find(" ",ind1)
    connect = float(line[ind1:ind2])
    ind1 = line.find("DATAREQUEST=")+12
    ind2 = line.find(" ",ind1)
    request = float(line[ind1:ind2])
    ind1 = line.find("DATACOMPLETE=")+13
    ind2 = line.find(" ",ind1)
    complete = float(line[ind1:ind2])-request
    ind1 = line.find("DATARESPONSE=")+13
    ind2 = line.find(" ",ind1)
    response = float(line[ind1:ind2])-request
    full.append(complete)
    firstByte.append(response)

def cf(d): return pylab.arange(1.0,float(len(d))+1.0)/float(len(d))

def getcdf(data, shownpercentile=0.99, maxpoints=100000.0):
    data.sort()
    frac = cf(data)
    k = len(data)/maxpoints
    x, y, lasty = [], [], 0.0
    for i in xrange(int(round(len(data)*shownpercentile))):
        if i % k > 1.0: continue
        assert not numpy.isnan(data[i])
        x.append(data[i])
        y.append(lasty)
        x.append(data[i])
        y.append(frac[i])
        lasty = frac[i]
    return x, y

x, y = getcdf(full)
pylab.plot(x, y, label="50KiB Full Download")
x, y = getcdf(firstByte)
pylab.plot(x, y, label="50KiB Time to first Byte")
pylab.axis([0,35,0.0,1.0])
pylab.legend(loc="lower right")
pylab.title("50KiB TorPerf")
pylab.show()


