SOURCES = util.ml syntax.ml evaluation.ml lexer.mll parser.mly print_x.ml main.ml
RESULT  = main.run

YFLAGS = -v

all: byte-code byte-code-library

-include OCamlMakefile
