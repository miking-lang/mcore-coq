OUTDIR=build

LATEXMK=latexmk -dvi- -ps- -pdf -pdflatex="texfot xelatex -synctex=1 -halt-on-error -interaction=nonstopmode -file-line-error --shell-escape %O %S" -outdir=$(OUTDIR)

.PHONY: all view clean

all:
	$(LATEXMK) main

view:
	$(LATEXMK) -pvc main

clean:
	rm -rf $(OUTDIR)
	latexmk -C main
