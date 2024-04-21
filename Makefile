all: run

run: main.ml lexer.mll parser.mly ast.ml ast_print.ml
	ocamllex lexer.mll
	ocamlyacc parser.mly
	rm parser.mli 
	ocamlc -c ast.ml
	ocamlc -c ast_print.ml
	ocamlc -c parser.ml 
	ocamlc -c lexer.ml 
	ocamlc -o main ast.cmo ast_print.cmo parser.cmo lexer.cmo main.ml 

test: run
	./main < test

clean:
	rm -f lexer.cmi lexer.cmo main.cmi main.cmo parser.cmi parser.cmo ast.cmi ast.cmo ast_print.cmi ast_print.cmo main lexer.ml parser.ml
