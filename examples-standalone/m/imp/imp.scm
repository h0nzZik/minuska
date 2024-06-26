(
 (language imp)
 (semantics imp.m)
 (parser_exe "imp-parser/_build/install/default/bin")
 (parser_builder "pushd imp-parser; dune build @all; popd")
)

