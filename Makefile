all: build

RocqMakefile:
	rocq makefile -f _RocqProject -o RocqMakefile

build: RocqMakefile
	make -f RocqMakefile

clean: RocqMakefile
	make -f RocqMakefile clean
	@rm RocqMakefile RocqMakefile.conf

.PHONY: build clean
