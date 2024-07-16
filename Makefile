

all: sols nosols

nosols:
	pdflatex --jobname="notes-nosol" "\newif\ifsol\solfalse\input{notes}" 
	pdflatex --jobname="notes-nosol" "\newif\ifsol\solfalse\input{notes}"

pdf:
	pdflatex notes.tex
	pdflatex notes.tex

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
