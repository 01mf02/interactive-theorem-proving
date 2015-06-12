REVEAL_THEME=night
REVEAL_CSS=reveal.js/css/theme/$(REVEAL_THEME).css

all: imps.html imps.pdf

%.html: %.md $(REVEAL_CSS)
	pandoc -t revealjs --self-contained --css $(REVEAL_CSS) $< -o $@

%.pdf: %.md
	pandoc -t beamer -i $< -o $@

clean:
	rm *.html *.pdf
