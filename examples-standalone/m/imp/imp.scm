(
 (language imp)
 (semantics imp.m)
 (parser_exe "imp-parser/_build/install/default/bin/imp-parser")
 (parser_builder "pushd imp-parser; dune build @all; popd")
)

