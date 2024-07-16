

all: sols nosols

nosols:
	pdflatex --jobname="notes-nosol" "\newif\ifsol\solfalse\input{notes}" 
	pdflatex --jobname="notes-nosol" "\newif\ifsol\solfalse\input{notes}"

pdf:
	pdflatex notes.tex
	pdflatex notes.tex
