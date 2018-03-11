#tl 2015:
# FROM thomasweise/texlive
# tl 2017; large
FROM sumdoc/texlive-2017
#FROM themoosemind/texlive-docker # Doesn't use dependencies latexmk kills it

RUN apt-get update -y && apt-get install -y --no-install-recommends \
  curl latexmk unzip xz-utils && \
  apt-get clean
  
# Possible alternatives that require different packaging:
# https://github.com/vansanblch/Inconsolata-LGC
# https://github.com/kiwi0fruit/Inconsolata-LGC
RUN mkdir -p /usr/share/fonts/Inconsolata && \
  curl -SL https://github.com/downloads/MihailJP/Inconsolata-LGC/InconsolataLGC-1.1.0.tar.xz \
  | tar -xJC /usr/share/fonts/Inconsolata

#
# Libertine Math retrieved from:
#

RUN mkdir -p /usr/share/fonts/Libertine && \
   curl -SL http://sourceforge.net/projects/linuxlibertine/files/linuxlibertine/5.3.0/LinLibertineOTF_5.3.0_2012_07_02.tgz/download \
   | tar -zxC /usr/share/fonts/Libertine && \
   curl -O https://fontlibrary.org/assets/downloads/libertinus-math/669b2b03ec50a970ff13c8f3009bd78c/libertinus-math.zip && \
   unzip libertinus-math.zip -d /usr/share/fonts/Libertine/ && \
   rm -f libertinus-math.zip
   

