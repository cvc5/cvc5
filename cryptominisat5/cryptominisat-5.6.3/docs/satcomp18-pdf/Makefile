TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
PRE =  $(TEX) -ini -job-name="preamble" "&pdflatex preamble.tex\dump"
BIB = bibtex

all: cmsv55.pdf

view :
	    okular cmsv55.pdf

cmsv55.pdf : clean cmsv55.tex cmsv55.bbl cmsv55.blg
	    $(TEX) cmsv55.tex
	    $(TEX) cmsv55.tex

cmsv55.bbl cmsv5.blg : cmsv55.bib cmsv55.aux
	    $(BIB) cmsv55

cmsv55.aux : cmsv55.tex
	    $(TEX) cmsv55.tex

cmsv55.bib : cmsv55.tex
	    $(TEX) cmsv55.tex

clean:
	rm -f *.log *.pdf *.blg *.bbl *.aux *.out *.backup
