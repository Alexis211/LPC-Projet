BIN=minic++

all: $(BIN)

$(BIN): main.byte
	cp main.byte minic++

main.byte: main.ml ast.ml parser.mly lexer.mll pretty.ml typing.ml pretty_typing.ml
	ocamlbuild main.byte

clean:
	rm -r _build
	rm main.byte
	rm $(BIN)
