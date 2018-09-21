TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
PRE =  $(TEX) -ini -job-name="preamble" "&pdflatex preamble.tex\dump"
BIB = bibtex

all: cmsv4.pdf

view :
	    open cmsv4.pdf

cmsv4.pdf : cmsv4.tex cmsv4.bbl cmsv4.blg
	    $(TEX) cmsv4.tex

cmsv4.bbl cmsv4.blg : cmsv4.bib cmsv4.aux
	    $(BIB) cmsv4

cmsv4.aux : cmsv4.tex
	    $(TEX) cmsv4.tex

cmsv4.bib : cmsv4.tex
	    $(TEX) cmsv4.tex

clean:
	rm -f *.aux *.bbl *.out cmsv4.pdf *.log *.blg
