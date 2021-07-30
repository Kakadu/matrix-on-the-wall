.PHONY: all watch demo

all:
	dune build prop/prop.exe --display=quiet && dune exec prop/prop.exe --display=quiet

watch:
	dune build prop/prop.exe -w

demo:
	dune build demo/d.exe && dune exec demo/d.exe --display=quiet

arith:
	dune build demo/arith.exe && dune exec demo/arith.exe --display=quiet

clean:
	@dune clean
