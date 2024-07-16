

all: sols nosols

nosols:
	pdflatex --jobname="CftLFP-nosol" "\newif\ifsol\solfalse\input{CftLFP}" 
	pdflatex --jobname="CftLFP-nosol" "\newif\ifsol\solfalse\input{CftLFP}"

pdf:
	pdflatex CftLFP.tex
	pdflatex CftLFP.tex

clean:
	@rm -f *.aux
	@rm -f *fdb_latexmk
	@rm -f *.fls
	@rm -f *.log
	@rm -f *.out
	@rm -f *.lof
	@rm -f *.lot
	@rm -f *.toc
	@rm -f *.fmt
	@rm -f *.fot
	@rm -f *.cb
	@rm -f *.cb2
