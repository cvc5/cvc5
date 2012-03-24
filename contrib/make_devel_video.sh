#!/bin/sh

# get the svn log
svn log -r 1:HEAD --xml --verbose --quiet > cvc4-log.xml

# run gource into ffmeg (first pass)
gource --key --max-file-lag -1 -i 0 --max-files 0 --hide progress -1280x720 --user-scale 1.5 --camera-mode track --title "cvc4 trunk" -s 0.5 -r 25 --date-format "%B %d, %Y" cvc4-log.xml -o - | ffmpeg -y -r 25 -f image2pipe -vcodec ppm -i - -vcodec libx264 -vpre ultrafast_firstpass -crf 1 -threads 0 -bf 0 -s 640x360 cvc4-640x360.mp4

# run gource into ffmeg (second pass)
gource --key --max-file-lag -1 -i 0 --max-files 0 --hide progress -1280x720 --user-scale 1.5 --camera-mode track --title "cvc4 trunk" -s 0.5 -r 25 --date-format "%B %d, %Y" cvc4-log.xml -o - | ffmpeg -y -r 25 -f image2pipe -vcodec ppm -i - -vcodec libx264 -vpre ultrafast -crf 1 -threads 0 -bf 0 -s 640x360 cvc4-640x360.mp4
