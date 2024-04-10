

all: sols nosols

sols:
	pdflatex --jobname="notes-sol" "\newif\ifsol\soltrue\input{notes}" 
	pdflatex --jobname="notes-sol" "\newif\ifsol\soltrue\input{notes}"

nosols:
	pdflatex notes.tex
	pdflatex notes.tex