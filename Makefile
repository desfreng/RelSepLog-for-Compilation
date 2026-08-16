PROJECT = RSL
SRC_DIR = theories

.PHONY: all build check clean

all: build

build:
	dune build

clean:
	dune clean
	rm -rf _build/

check: build
	find _build/default/$(SRC_DIR) -name "*.vo" -print0 | xargs -0 rocqchk -R _build/default/$(SRC_DIR) $(PROJECT) -silent -o

report: report/report.tex report/macro.tex
	latexmk -pdf -cd -outdir=./_build/report/ report/report.tex
