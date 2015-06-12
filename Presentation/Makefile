all: imps.html imps.pdf

%.html: %.md
	pandoc -t revealjs --self-contained --css reveal.js/css/theme/night.css $< -o $@

%.pdf: %.md
	pandoc -t beamer -i $< -o $@

clean:
	rm *.html *.pdf
