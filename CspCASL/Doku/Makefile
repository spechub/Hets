TARGET = CSP_CASL_Parser

PS2PDF = ps2pdf -sPAPERSIZE=a4

default:		$(TARGET).dvi

clean:
			@find . -name '*~' -exec rm -vf {} ';'

nuke:			clean
			@find . -name '*.aux' -exec rm -vf {} ';'
			@find . -name '*.dvi' -exec rm -vf {} ';'
			@find . -name '*.ps' -exec rm -vf {} ';'
			@find . -name '*.pdf' -exec rm -vf {} ';'
			@find . -name '*.log' -exec rm -vf {} ';'
			@find . -name '*.toc' -exec rm -vf {} ';'
			@find . -name '*.fig.bak' -exec rm -vf {} ';'

$(TARGET).dvi:		$(TARGET).tex
			latex $(TARGET).tex
			latex $(TARGET).tex

$(TARGET).ps:		$(TARGET).dvi
			dvips -o $(TARGET).ps $(TARGET).dvi

$(TARGET).2up.ps:	$(TARGET).ps
			psnup -m20 -d1 -2 $(TARGET).ps $(TARGET).2up.ps

$(TARGET).pdf:		$(TARGET).ps
			$(PS2PDF) $(TARGET).ps $(TARGET).pdf

$(TARGET).2up.pdf:	$(TARGET).2up.ps
			$(PS2PDF) $(TARGET).2up.ps $(TARGET).2up.pdf

dvi:			$(TARGET).dvi

ps:			$(TARGET).ps

pdf:			$(TARGET).pdf

2up:			$(TARGET).2up.ps $(TARGET).2up.pdf

all:			dvi ps pdf 2up

xdvi:			$(TARGET).dvi
			xdvi $(TARGET).dvi &

gv:			$(TARGET).ps
			gv $(TARGET).ps &

acro:			$(TARGET).pdf
			acroread $(TARGET).pdf &
