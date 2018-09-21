TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error
PRE =  $(TEX) -ini -job-name="preamble" "&pdflatex preamble.tex\dump"
BIB = bibtex

all: cmsv5.pdf

view :
	    okular cmsv5.pdf

cmsv5.pdf : clean cmsv5.tex cmsv5.bbl cmsv5.blg
	    $(TEX) cmsv5.tex
	    $(TEX) cmsv5.tex
		mv cmsv5.pdf cmsv54.pdf

cmsv5.bbl cmsv5.blg : cmsv5.bib cmsv5.aux
	    $(BIB) cmsv5

cmsv5.aux : cmsv5.tex
	    $(TEX) cmsv5.tex

cmsv5.bib : cmsv5.tex
	    $(TEX) cmsv5.tex

clean:
	rm -f *.log *.pdf *.blg *.bbl *.aux *.out *.backup
