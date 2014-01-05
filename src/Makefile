BIN=minic++

all: $(BIN)

$(BIN): main.ml ast.ml parser.mly lexer.mll pretty.ml typing.ml pretty_typing.ml codegen.ml
	ocamlbuild main.native
	mv main.native $(BIN)

clean:
	rm -r _build
	rm $(BIN)
