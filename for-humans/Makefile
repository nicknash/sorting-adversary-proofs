.PHONY: all clean checks submission

all: output/pdf/paper.pdf

output/pdf/paper.pdf: paper.tex $(wildcard sections/*.tex)
	mkdir -p build output/pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper.tex
	cp build/paper.pdf $@

checks:
	python3 anc/check_finite_digits.py
	python3 anc/check_controller.py
	python3 anc/check_interval_certificates.py
	python3 anc/check_simplification.py
	python3 anc/check_packing_primitives.py --output anc/check_packing_primitives.json

submission: output/pdf/paper.pdf
	python3 package_submission.py

clean:
	rm -rf build
