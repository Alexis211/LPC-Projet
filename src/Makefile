BIN=minic++

all: $(BIN)

$(BIN): main.ml ast.ml parser.mly lexer.mll pretty.ml typing.ml pretty_typing.ml
	ocamlbuild main.byte
	mv main.byte minic++

clean:
	rm -r _build
	rm main.byte
	rm $(BIN)
