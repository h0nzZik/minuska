(
 (language imp)
 (semantics imp.m)
 (parser_exe "parser/_build/install/default/bin/parser")
 (parser_builder "pushd parser; dune build @all; popd")
)

