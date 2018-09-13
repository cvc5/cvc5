#!/usr/bin/env python

import sys
of = sys.argv[1]
f = open(of, "r")
text = f.read()
mylines = text.splitlines()
i = 0;
time = []
for line in mylines :
  time.append(float(line))
  #print "t:%f" %(time[i])
  i += 1

lastnum = -1
for a in range(0, 60000, 1) :
  num = 0
  for t in time :
    #print "t: %f a: %d" %(t, a)
    if (t < a) :
      num += 1
  
  if (lastnum != num) :
      print "%d \t%d" %(num, a)
  lastnum = num

f.close();
