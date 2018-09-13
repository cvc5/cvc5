TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
PRE =  $(TEX) -ini -job-name="preamble" "&pdflatex preamble.tex\dump"
BIB = bibtex

all: cmsv4.pdf

view :
	    okular cmsv44.pdf

cmsv4.pdf : clean cmsv4.tex cmsv4.bbl cmsv4.blg
	    $(TEX) cmsv4.tex
	    $(TEX) cmsv4.tex
		mv cmsv4.pdf cmsv44.pdf

cmsv4.bbl cmsv4.blg : cmsv4.bib cmsv4.aux
	    $(BIB) cmsv4

cmsv4.aux : cmsv4.tex
	    $(TEX) cmsv4.tex

cmsv4.bib : cmsv4.tex
	    $(TEX) cmsv4.tex

clean:
	rm -f *.log *.pdf *.blg *.bbl *.aux *.out
