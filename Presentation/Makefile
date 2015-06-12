all: imps.html

%.html: %.md
	pandoc -t revealjs --self-contained --css reveal.js/css/theme/night.css $< -o $@
