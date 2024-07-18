

pdf:
	pdflatex -shell-escape CftLFP.tex
	pdflatex -shell-escape CftLFP.tex
	@rm -f *.tmp
	@rmdir _minted-*
	
nosols:
	pdflatex -shell-escape --jobname="CftLFP-nosol" "\newif\ifsol\solfalse\input{CftLFP}" 
	pdflatex -shell-escape --jobname="CftLFP-nosol" "\newif\ifsol\solfalse\input{CftLFP}"


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
